################################################################################
# Description: Grammar based generation/fuzzer
# Author: Jesse Schwartzentruber
#
# Copyright 2014 BlackBerry Limited
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
#    Unless required by applicable law or agreed to in writing, software
#    distributed under the License is distributed on an "AS IS" BASIS,
#    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#    See the License for the specific language governing permissions and
#    limitations under the License.
################################################################################
# Language Defn Syntax
# ====================
#
# SymName         Def1 [Def2] (concat)
# SymName{a,b}    Def (repeat, between a-b instances)
# SymName   1     Def1 (either Def1 (1:3 odds) or Def2 (2:3))
#           2     Def2
# SymName         /[A-Za-z]*..+[^a-f]{2}/ (simple regex)
# SymName         @SymName1   (returns a previously defined instance of SymName1)
# FuncCall        rndint(a,b) (rndint, rndflt are built-in, others can be passed as keyword args to the Grammar constructor)
#
#
# suggestions (not working):
# SymName{a,b} 1 Def1 (combine repeat and choice, has the additional property that each defn will only be used at most once)
#              1 Def2
################################################################################

import binascii
import logging as log
import io
import os
import random
import re


DEFAULT_LIMIT = 100 * 1024

if bool(os.getenv("DEBUG")):
    log.getLogger().setLevel(log.DEBUG)


class GrammarException(Exception):
    pass
class ParseError(GrammarException):
    pass
class IntegrityError(GrammarException):
    pass
class GenerationError(GrammarException):
    pass


class _GenState(object):

    def __init__(self, grmr):
        self.symstack = []
        self.instances = {}
        self.output = []
        self.grmr = grmr
        self.length = 0


class WeightedChoice(object):

    def __init__(self, iterable=None):
        self.total = 0.0
        self.values = []
        self.weights = []
        if iterable is not None:
            self.extend(iterable)

    def extend(self, iterable):
        for v in iterable:
            self.append(*v)

    def append(self, value, weight=1):
        self.total += weight
        self.values.append(value)
        self.weights.append(weight)

    def choice(self):
        target = random.uniform(0, self.total)
        for w, v in zip(self.weights, self.values):
            target -= w
            if target < 0:
                return v
        raise GenerationError("Too much total weight? remainder is %0.2f from %0.2f total" % (target, self.total))

    def __repr__(self):
        return "WeightedChoice(%s)" % tuple(zip(self.values, self.weights))


class Grammar(object):
    """Generate a language conforming to a given grammar specification.

    A Grammar consists of a set of symbol definitions which are used to define the structure of a language. The Grammar
    object is created from a text input with the format described below, and then used to generate randomly constructed
    instances of the described language. The entrypoint of the grammar is the named symbol 'root'. Comments are allowed
    anywhere in the file, preceded by a hash character (``#``).

    Symbols can either be named or implicit. A named symbol consists of a symbol name at the beginning of a line,
    followed by at least one whitespace character, followed by the symbol definition.

        ::

            SymbolName  Definition

    Implicit symbols are defined without being assigned an explicit name. For example a regular expression can be used
    in a concatenation definition directly, without being assigned a name. Choice and repeat symbols cannot be defined
    implicitly.

    **Concatenation**:

            ::

                SymbolName      SubSymbol1 [SubSymbol2] ...

        A concatenation consists of one or more symbols which will be generated in succession. The sub-symbol can be
        any named symbol, reference, or an implicit declaration of allowed symbol types. A concatenation can also be
        implicitly defined as the sub-symbol of a choice or repeat symbol.

    **Choice**: (must be named, not implicit)

            ::

                SymbolName      Weight1     SubSymbol1
                               [Weight2     SubSymbol2]
                               [Weight3     SubSymbol3]

        A choice consists of one or more weighted sub-symbols. At generation, only one of the sub-symbols will be
        generated at random, with each sub-symbol being generated with probability of weight/sum(weights) (the sum of
        all weights in this choice). Weight can be a non-negative number.

    **Repeat**: (must be named, not implicit)

            ::

                SymbolName      {Min,Max}   SubSymbol

        Defines a repetition of a sub-symbol. The number of repetitions is at most ``Max``, and at minimum ``Min``.

    **Text**:

            ::

                SymbolName      'some text'
                SymbolName      "some text"

        A text symbol is a string generated verbatim in the output. A few escape codes are recognized:
            * ``\\t``  horizontal tab (ASCII 0x09)
            * ``\\n``   line feed (ASCII 0x0A)
            * ``\\v``  vertical tab (ASCII 0x0B)
            * ``\\r``  carriage return (ASCII 0x0D)
        Any other character preceded by backslash will appear in the output without the backslash (including backslash,
        single quote, and double quote).

    **Regular expression**:

            ::

                SymbolName      /[a-zA][0-9]*.+[^0-9]{2}.[^abc]{1,3}/

        A regular expression (regex) symbol is a minimal regular expression implementation used for generating text
        patterns (rather than the traditional use for matching text patterns). A regex symbol consists of one or more
        parts in succession, and each part consists of a character set definition optionally followed by a repetition
        specification. The character set definition can be a period ``.`` to denote any character, a set of characters in
        brackets eg. ``[0-9a-f]``, or an inverted set of characters ``[^a-z]`` (any character except a-z). As shown, ranges can
        be used by using a dash. The dash character can be matched in a set by putting it last in the brackets. The
        optional repetition specification can be a range of integers in curly braces, eg. ``{1,10}`` will generate between
        1 and 10 repetitions (at random), a single integer in curly braces, eg. ``{10}`` will generate exactly 10
        repetitions, an asterisk character (``*``) which is equivalent to ``{0,5}``, or a plus character (``+``) which is
        equivalent to ``{1,5}``.

    **Random floating point decimal**:

            ::

                SymbolName      rndflt(a,b)

        A random floating-point decimal number between ``a`` and ``b`` inclusive.

    **Random integer**:

            ::

                SymbolName      rndint(a,b)

        A random integer between ``a`` and ``b`` inclusive.

    **Reference**:

            ::

                SymbolRef       @SymbolName

        Symbol references allow a generated symbol to be used elsewhere in the grammar. Referencing a symbol by
        ``@Symbol`` will output a generated value of ``Symbol`` from elsewhere in the output.

    **Filter function**:

            ::

                SymbolName      function(SymbolArg1[,...])

        This denotes an externally defined filter function. Note that the function name can be any valid Python
        identifier. The function can take an arbitrary number of arguments, but must return a single string which is
        the generated value for this symbol instance. Functions are passed as keyword arguments into the Grammar object
        constructor.

    """
    _RE_LINE = re.compile(r"""
                           ^(?P<broken>.*)\\$ |
                           ^\s*(?P<comment>\#).*$ |
                           ^(?P<nothing>\s*)$ |
                           ^(?P<name>[\w-]+)(?P<type>\s*((?P<weight>[\d.]+)|\||\{\s*(?P<a>\d+)\s*(,\s*(?P<b>\d+)\s*)?\})\s*|\s+)(?P<def>.+)$ |
                           ^\s+(\||(?P<contweight>[\d.]+))\s*(?P<cont>.+)$
                           """, re.VERBOSE)

    def __init__(self, grammar="", limit=DEFAULT_LIMIT, **kwargs):
        sym = None
        self._limit = limit
        self._start = None
        self.symtab = {}
        self.tracked = set()
        self.funcs = kwargs
        if "rndint" not in self.funcs:
            self.funcs["rndint"] = lambda a, b: str(random.randint(int(a), int(b)))
        if "rndflt" not in self.funcs:
            self.funcs["rndflt"] = lambda a, b: str(random.uniform(float(a), float(b)))
        if not isinstance(grammar, io.IOBase):
            grammar = io.StringIO(grammar.decode() if isinstance(grammar, bytes) else grammar)
        ljoin = ""
        for line_no, line in enumerate(grammar, 1):
            self.n_implicit = -1
            log.debug("parsing line # %d: %s", line_no, line.rstrip())
            m = Grammar._RE_LINE.match(ljoin + line)
            if m is None:
                raise ParseError("Parse error on line %d" % line_no)
            if m.group("broken") is not None:
                ljoin = m.group("broken")
                continue
            ljoin = ""
            if m.group("comment") or m.group("nothing") is not None:
                continue
            if m.group("name"):
                sym_name, sym_type, sym_def = m.group("name", "type", "def")
                sym_type = sym_type.lstrip()
                if sym_type.startswith("|") or m.group("weight"):
                    # choice
                    weight = float(m.group("weight")) if m.group("weight") else 1
                    sym = ChoiceSymbol(sym_name, line_no, self)
                    sym.append(Symbol.parse(sym_def, line_no, self), weight, self)
                elif sym_type.startswith("{"):
                    # repeat
                    a, b = m.group("a", "b")
                    a = int(a)
                    b = int(b) if b else a
                    sym = RepeatSymbol(sym_name, a, b, line_no, self)
                    sym.extend(Symbol.parse(sym_def, line_no, self))
                else:
                    # sym def
                    sym = ConcatSymbol.parse(sym_name, sym_def, line_no, self)
                self.symtab[sym_name] = sym
            else:
                # continuation of choice
                if sym is None or not isinstance(sym, ChoiceSymbol):
                    raise ParseError("Unexpected continuation of choice symbol on line %d" % line_no)
                weight = float(m.group("contweight")) if m.group("contweight") else 1
                sym.append(Symbol.parse(m.group("cont"), line_no, self), weight, self)

        # sanity check
        funcs_used = {"rndflt", "rndint"}
        for name, sym in self.symtab.items():
            if isinstance(sym, AbstractSymbol):
                raise IntegrityError("Symbol %s used on line %d but not defined" % (name, sym.line_no))
            elif isinstance(sym, FuncSymbol):
                if sym.fname not in self.funcs:
                    raise IntegrityError("Function %s used on line %d but not defined" % (sym.fname, sym.line_no))
                funcs_used.add(sym.fname)
        if set(self.funcs.keys()) != funcs_used:
            unused_kwds = tuple(set(self.funcs.keys()) - funcs_used)
            raise IntegrityError("Unused keyword argument%s: %s" % ("s" if len(unused_kwds) > 1 else "", unused_kwds))
        syms_used = {"root"}
        to_check = {"root"}
        checked = set()
        while to_check:
            sym = self.symtab[to_check.pop()]
            checked.add(sym.name)
            children = set()
            if isinstance(sym, FuncSymbol):
                children = set(sym.args)
            elif isinstance(sym, (ConcatSymbol, RepeatSymbol)):
                children = set(sym)
            elif isinstance(sym, ChoiceSymbol):
                for child in sym.values:
                    children |= set(child)
            elif isinstance(sym, RegexSymbol):
                children = set(sym.parts)
            elif isinstance(sym, RefSymbol):
                children = {sym.ref}
            log.debug("%s is %s with %d children", sym.name, type(sym).__name__, len(children))
            syms_used |= children
            to_check |= children - checked
        if set(self.symtab.keys()) != syms_used:
            unused_syms = tuple(set(self.symtab.keys()) - syms_used)
            used_syms = tuple(syms_used)
            raise IntegrityError("Unused symbol%s: %s, Used symbol%s: %s" % ("s" if len(unused_syms) > 1 else "", unused_syms,
                                                                             "s" if len(used_syms) > 1 else "", used_syms))

    def is_limit_exceeded(self, length):
        return self._limit is not None and length >= self._limit

    def implicit(self):
        self.n_implicit += 1
        return self.n_implicit

    def generate(self, start="root"):
        if not isinstance(start, _GenState):
            gstate = _GenState(self)
            gstate.symstack = [start]
            gstate.instances = {s: [] for s in self.tracked}
        else:
            gstate = start
        tracking = []
        while gstate.symstack:
            this = gstate.symstack.pop()
            if isinstance(this, tuple):
                if this[0] != "untrack":
                    raise GenerationError("TODO meaningful error message")
                tracked = tracking.pop()
                if this[1] != tracked[0]:
                    raise GenerationError("TODO meaningful error message")
                instance = "".join(gstate.output[tracked[1]:])
                gstate.instances[this[1]].append(instance)
                continue
            if this in self.tracked: # need to capture everything generated by this symbol and add to "instances"
                gstate.symstack.append(("untrack", this))
                tracking.append((this, len(gstate.output)))
            self.symtab[this].generate(gstate)
        try:
            return "".join(gstate.output)
        except TypeError:
            return b"".join(gstate.output)


class Symbol(object):
    _RE_DEFN = re.compile(r"""
                           ^(?P<quote>["']) |
                           ^(?P<hexstr>x["']) |
                           ^(?P<regex>/) |
                           ^(?P<infunc>[,)]) |
                           ^(?P<comment>\#).* |
                           ^(?P<func>\w+)\( |
                           ^@(?P<ref>[\w-]+) |
                           ^(?P<sym>[\w-]+) |
                           ^(?P<ws>\s+)""", re.VERBOSE)

    def __init__(self, name, line_no, grmr=None):
        self.name = name
        self.line_no = line_no
        if grmr is not None:
            if name in grmr.symtab and not isinstance(grmr.symtab[name], (AbstractSymbol, RefSymbol)):
                raise ParseError("Redefinition of symbol %s on line %d (previously declared on line %d)" % (name, line_no, grmr.symtab[name].line_no))
            grmr.symtab[name] = self

    def generate(self, gstate):
        raise GenerationError("Can't generate symbol %s of type %s" % (self.name, type(self)))

    def match(self, inp, ptr):
        return 0

    @staticmethod
    def _parse(defn, line_no, grmr, in_func):
        result = []
        while defn:
            m = Symbol._RE_DEFN.match(defn)
            if m is None:
                raise ParseError("Failed to parse definition on line %d at: %s" % (line_no, defn))
            log.debug("parsed %s from %s", {k: v for k, v in m.groupdict().items() if v is not None}, defn)
            if m.group("ws") is not None:
                defn = defn[m.end(0):]
                continue
            if m.group("quote"):
                sym, defn = TextSymbol.parse(defn, line_no, grmr)
            elif m.group("hexstr"):
                sym, defn = BinSymbol.parse(defn, line_no, grmr)
            elif m.group("regex"):
                sym, defn = RegexSymbol.parse(defn, line_no, grmr)
            elif m.group("func"):
                defn = defn[m.end(0):]
                sym, defn = FuncSymbol.parse(m.group("func"), defn, line_no, grmr)
            elif m.group("ref"):
                sym = RefSymbol(m.group("ref"), line_no, grmr)
                defn = defn[m.end(0):]
            elif m.group("sym"):
                try:
                    sym = grmr.symtab[m.group("sym")]
                except KeyError:
                    sym = AbstractSymbol(m.group("sym"), line_no, grmr)
                defn = defn[m.end(0):]
            elif m.group("comment"):
                defn = ""
                break
            elif m.group("infunc"):
                if not in_func:
                    raise ParseError("Unexpected token in definition on line %d at: %s" % (line_no, defn))
                break
            result.append(sym.name)
        return result, defn

    @staticmethod
    def parse_func_arg(defn, line_no, grmr):
        return Symbol._parse(defn, line_no, grmr, True)

    @staticmethod
    def parse(defn, line_no, grmr):
        res, remain = Symbol._parse(defn, line_no, grmr, False)
        if remain:
            raise ParseError("TODO meaningful error message")
        return res


class AbstractSymbol(Symbol):

    def __init__(self, name, line_no, grmr):
        Symbol.__init__(self, name, line_no, grmr)
        log.debug("\tabstract %s", name)


class BinSymbol(Symbol):
    _RE_QUOTE = re.compile(r'''(?P<end>["'])''')

    def __init__(self, value, line_no, grmr):
        name = "[bin (line %d #%d)]" % (line_no, grmr.implicit())
        Symbol.__init__(self, name, line_no, grmr)
        self.value = binascii.unhexlify(value)
        log.debug("\tbin %s: %s", name, value)

    def generate(self, gstate):
        gstate.output.append(self.value)
        gstate.length += len(self.value)

    def match(self, inp, ptr):
        # returns the length of matching input (0 for no match)
        if inp.startswith(self.value, ptr):
            return len(self.value)
        return 0

    @staticmethod
    def parse(defn, line_no, grmr):
        x, qchar, defn = defn[0], defn[1], defn[2:]
        if x != "x":
            raise ParseError("TODO meaningful error message")
        if qchar not in "'\"":
            raise ParseError("TODO meaningful error message")
        enquo = defn.find(qchar)
        if enquo == -1:
            raise ParseError("Unterminated bin literal!")
        value, defn = defn[:enquo], defn[enquo+1:]
        sym = BinSymbol(value, line_no, grmr)
        return sym, defn


class TextSymbol(Symbol):
    _RE_QUOTE = re.compile(r'''(?P<end>["'])|\\(?P<esc>.)''')

    def __init__(self, value, line_no, grmr):
        name = "[text (line %d #%d)]" % (line_no, grmr.implicit())
        Symbol.__init__(self, name, line_no, grmr)
        self.value = value
        log.debug("\ttext %s: %s", name, value)

    def generate(self, gstate):
        gstate.output.append(self.value)
        gstate.length += len(self.value)

    def match(self, inp, ptr):
        # returns the length of matching input (0 for no match)
        if inp.startswith(self.value, ptr):
            return len(self.value)
        return 0

    @staticmethod
    def parse(defn, line_no, grmr):
        qchar, defn = defn[0], defn[1:]
        if qchar not in "'\"":
            raise ParseError("TODO meaningful error message")
        out, last = [], 0
        for m in TextSymbol._RE_QUOTE.finditer(defn):
            out.append(defn[last:m.start(0)])
            last = m.end(0)
            if m.group("end") == qchar:
                break
            elif m.group("end"):
                out.append(m.group("end"))
            else:
                try:
                    out.append({"n": "\n",
                                "r": "\r",
                                "t": "\t",
                                "v": "\v"}[m.group("esc")])
                except KeyError:
                    out.append(m.group("esc"))
        else:
            raise ParseError("Unterminated string literal!")
        defn = defn[last:]
        sym = TextSymbol("".join(out), line_no, grmr)
        return sym, defn


class ConcatSymbol(Symbol, list):

    def __init__(self, name, line_no, grmr):
        Symbol.__init__(self, name, line_no, grmr)
        list.__init__(self)
        log.debug("\tconcat %s", name)

    def generate(self, gstate):
        gstate.symstack.extend(reversed(self))

    @staticmethod
    def parse(name, defn, line_no, grmr):
        result = ConcatSymbol(name, line_no, grmr)
        result.extend(Symbol.parse(defn, line_no, grmr))
        return result


class ChoiceSymbol(Symbol, WeightedChoice):

    def __init__(self, name, line_no, grmr):
        Symbol.__init__(self, name, line_no, grmr)
        WeightedChoice.__init__(self)
        log.debug("\tchoice %s", name)

    def append(self, value, weight, grmr):
        if len(value) == 1 and isinstance(grmr.symtab[value[0]], WeightedChoice):
            weight = grmr.symtab[value[0]].total
        WeightedChoice.append(self, value, weight)

    def generate(self, gstate):
        gstate.symstack.extend(reversed(self.choice()))


class FuncSymbol(Symbol):

    def __init__(self, name, line_no, grmr):
        sname = "[%s (line %d #%d)]" % (name, line_no, grmr.implicit())
        Symbol.__init__(self, sname, line_no, grmr)
        self.fname = name
        self.args = []

    def generate(self, gstate):
        args = []
        for arg in self.args:
            astate = _GenState(gstate.grmr)
            astate.symstack = [arg]
            astate.instances = gstate.instances
            args.append(gstate.grmr.generate(astate))
        gstate.output.append(gstate.grmr.funcs[self.fname](*args))
        gstate.length += len(gstate.output[-1])

    @staticmethod
    def parse(name, defn, line_no, grmr):
        result = FuncSymbol(name, line_no, grmr)
        done = False
        while not done:
            arg, defn = Symbol.parse_func_arg(defn, line_no, grmr)
            if defn[0] not in ",)":
                raise ParseError("TODO meaningful error message")
            done = defn[0] == ")"
            defn = defn[1:]
            if arg or not done:
                sym = ConcatSymbol("%s.%s]" % (result.name[:-1], len(result.args)), line_no, grmr)
                sym.extend(arg)
                result.args.append(sym.name)
        return result, defn


class RefSymbol(Symbol):

    def __init__(self, ref, line_no, grmr):
        Symbol.__init__(self, "@%s" % ref, line_no, grmr)
        if ref not in grmr.symtab:
            grmr.symtab[ref] = AbstractSymbol(ref, line_no, grmr)
        self.ref = ref
        grmr.tracked.add(ref)
        log.debug("\tref %s", ref)

    def generate(self, gstate):
        if gstate.instances[self.ref]:
            gstate.output.append(random.choice(gstate.instances[self.ref]))
            gstate.length += len(gstate.output[-1])
        else:
            log.debug("No instances of %s yet, generating one instead of a reference", self.ref)
            gstate.grmr.symtab[self.ref].generate(gstate)


class RepeatSymbol(Symbol, list):

    def __init__(self, name, a, b, line_no, grmr):
        Symbol.__init__(self, name, line_no, grmr)
        list.__init__(self)
        self.a, self.b = a, b
        log.debug("\trepeat %s", name)

    def generate(self, gstate):
        if gstate.grmr.is_limit_exceeded(gstate.length):
            return
        n = random.randint(self.a, random.randint(self.a, self.b)) # roughly betavariate(0.75, 2.25)
        gstate.symstack.extend(n * tuple(reversed(self)))


class RegexSymbol(Symbol):
    _REGEX_ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZ" \
                      "abcdefghijklmnopqrstuvwxyz" \
                      "0123456789" \
                      ",./<>?;':\"[]\\{}|=_+`~!@#$%^&*() -"
    _RE_REPEAT = re.compile(r"^\{\s*(?P<a>\d+)\s*(,\s*(?P<b>\d+)\s*)?\}")

    def __init__(self, line_no, grmr):
        name = "[regex (line %d #%d)]" % (line_no, grmr.implicit())
        Symbol.__init__(self, name, line_no, grmr)
        self.parts = []
        self.n_implicit = 0
        log.debug("\tregex %s", name)

    def new_choice(self, grmr):
        name = "%s.%s]" % (self.name[:-1], self.n_implicit)
        self.n_implicit += 1
        return ChoiceSymbol(name, self.line_no, grmr)

    def add_repeat(self, sym, a, b, grmr):
        name = "%s.%s]" % (self.name[:-1], self.n_implicit)
        self.n_implicit += 1
        rep = RepeatSymbol(name, a, b, self.line_no, grmr)
        rep.append(sym.name)
        self.parts.append(name)

    def generate(self, gstate):
        gstate.symstack.extend(reversed(self.parts))

    @staticmethod
    def parse(defn, line_no, grmr):
        result = RegexSymbol(line_no, grmr)
        c = 1
        sym = None
        if defn[0] != "/":
            raise ParseError("TODO meaningful error message")
        while c < len(defn):
            if defn[c] == "/":
                if sym is not None:
                    result.parts.append(sym.name)
                return result, defn[c+1:]
            elif defn[c] == "[":
                # range
                if sym is not None:
                    result.parts.append(sym.name)
                sym = result.new_choice(grmr)
                inverse = defn[c+1] == "^"
                c += 2 if inverse else 1
                alpha = []
                while c < len(defn):
                    if defn[c] == "\\":
                        alpha.append(defn[c+1])
                        c += 2
                    elif defn[c] == "]":
                        c += 1
                        break
                    else:
                        alpha.append(defn[c])
                        c += 1
                    if len(alpha) >= 3 and alpha[-2] == "-":
                        # expand range
                        start, end, alpha = alpha[-3], alpha[-1], alpha[:-3]
                        alpha.extend(chr(l) for l in range(ord(start), ord(end)+1))
                        if alpha[-1] == "-": # move this so we don't end up expanding a false range (not a bullet-proof solution)
                            alpha = alpha[-1] + alpha[:-1]
                else:
                    break
                alpha = set(alpha)
                if inverse:
                    alpha = set(RegexSymbol._REGEX_ALPHABET) - alpha
                for s in alpha:
                    sym.append([TextSymbol(s, line_no, grmr).name], 1, grmr)
            elif defn[c] == ".":
                # any one thing
                if sym is not None:
                    result.parts.append(sym.name)
                c += 1
                try:
                    sym = grmr.symtab["[regex alpha]"]
                except KeyError:
                    sym = ChoiceSymbol("[regex alpha]", 0, grmr)
                    for s in RegexSymbol._REGEX_ALPHABET:
                        sym.append([TextSymbol(s, 0, grmr).name], 1, grmr)
            elif defn[c] == "\\":
                # escape
                if sym is not None:
                    result.parts.append(sym.name)
                sym = TextSymbol(defn[c+1], line_no, grmr)
                c += 2
            elif defn[c] == "+":
                if sym is None:
                    raise ParseError("TODO meaningful error message")
                c += 1
                result.add_repeat(sym, 1, 5, grmr)
                sym = None
            elif defn[c] == "*":
                if sym is None:
                    raise ParseError("TODO meaningful error message")
                result.add_repeat(sym, 0, 5, grmr)
                c += 1
                sym = None
            elif defn[c] == "{":
                if sym is None:
                    raise ParseError("TODO meaningful error message")
                m = RegexSymbol._RE_REPEAT.match(defn[c:])
                if m is None:
                    raise ParseError("TODO meaningful error message")
                a = int(m.group("a"))
                b = int(m.group("b")) if m.group("b") else a
                result.add_repeat(sym, a, b, grmr)
                c += m.end(0)
                sym = None
            else:
                # bare char
                if sym is not None:
                    result.parts.append(sym.name)
                sym = TextSymbol(defn[c], line_no, grmr)
                c += 1
        raise ParseError("Unterminated regular expression")


if __name__ == "__main__":
    import argparse
    import os.path
    import sys

    argp = argparse.ArgumentParser(description="Generate a testcase from a grammar")
    argp.add_argument("input", type=argparse.FileType('r'), help="Input grammar definition")
    argp.add_argument("output", type=argparse.FileType('w'), nargs="?", default=sys.stdout, help="Output testcase")
    argp.add_argument("-f", "--function", action="append", nargs=2, help="Function used in the grammar (eg. -f filter lambda x:x.replace('x','y')", default=[])
    argp.add_argument("-l", "--limit", type=int, default=DEFAULT_LIMIT, help="Set a generation limit (roughly)")
    args = argp.parse_args()
    args.function = {func: eval(defn) for (func, defn) in args.function}
    args.output.write(Grammar(args.input.read(), limit=args.limit, **args.function).generate())

