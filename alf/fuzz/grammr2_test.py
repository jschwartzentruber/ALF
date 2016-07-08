################################################################################
# Description: Grammr2 tests
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
from grammr2 import Grammar, WeightedChoice, ParseError, IntegrityError
import os
import re
import shutil
import tempfile
import unittest

class GrammarTests(unittest.TestCase):

    def test_broken(self):
        w = Grammar("root 'a' 'b'\\\n"
                    "     'c'\n")
        self.assertEqual(w.generate(), "abc")

    def test_wchoice(self):
        iters = 10000
        w = WeightedChoice([(1, 1), (2, 1), (3, 1)])
        r = {1:0, 2:0, 3:0}
        for _ in range(iters):
            r[w.choice()] += 1
        for v in r.values():
            self.assertAlmostEqual(v/iters, 1/3, delta=.02)
        w = WeightedChoice([(1, 1), (2, 2), (3, 1)])
        r = {1:0, 2:0, 3:0}
        for _ in range(iters):
            r[w.choice()] += 1
        self.assertAlmostEqual(float(r[1])/iters, 0.25, delta=.02)
        self.assertAlmostEqual(float(r[2])/iters, 0.5, delta=.02)
        self.assertAlmostEqual(float(r[3])/iters, 0.25, delta=.02)
        w = WeightedChoice([(1, 3), (2, 1), (3, 1)])
        r = {1:0, 2:0, 3:0}
        for _ in range(iters):
            r[w.choice()] += 1
        self.assertAlmostEqual(float(r[1])/iters, 0.6, delta=.02)
        self.assertAlmostEqual(float(r[2])/iters, 0.2, delta=.02)
        self.assertAlmostEqual(float(r[3])/iters, 0.2, delta=.02)
        w = WeightedChoice([(1, 1), (2, 1), (3, 4)])
        r = {1:0, 2:0, 3:0}
        for _ in range(iters):
            r[w.choice()] += 1
        self.assertAlmostEqual(float(r[1])/iters, 1.0/6, delta=.02)
        self.assertAlmostEqual(float(r[2])/iters, 1.0/6, delta=.02)
        self.assertAlmostEqual(float(r[3])/iters, 2.0/3, delta=.02)

    def test_funcs(self):
        iters = 10
        gram = "root    {1,10}  func\n" \
               "func    1       'z' zero(nuvar) '\\n'\n" \
               "        1       'a' alpha(alvar , '*,' rep) '\\n'\n" \
               "        1       nuvar '\\n'\n" \
               "        1       alvar '\\n'\n" \
               "nuvar           'n' /[0-9]{6}/\n" \
               "alvar           'c' /[a-z]{6}/\n" \
               "rep             /[0-9]/"
        def zero(inp):
            return inp.replace("0", "z")
        def alpha(inp, rep):
            return "%s/%s" % (rep, inp.replace("a", rep))
        w = Grammar(gram, zero=zero, alpha=alpha)
        i = 0
        while i < iters:
            i += 1
            for line in w.generate().splitlines():
                if line.startswith("zn"):
                    self.assertRegexpMatches(line[2:], r"^[1-9z]{6}$")
                elif line.startswith("a"):
                    self.assertRegexpMatches(line[1:], r"^(\*,[0-9])/c(\1|[b-z]){6}$")
                elif line.startswith("n"):
                    self.assertRegexpMatches(line[1:], r"^[0-9]{6}$")
                elif line.startswith("c"):
                    self.assertRegexpMatches(line[1:], r"^[a-z]{6}$")
                else:
                    raise Exception("unexpected line: %s" % line)

    def test_basic(self):
        w = Grammar("root    ok\n"
                    "ok      '1'")
        self.assertEqual(w.generate(), "1")
        w = Grammar("root   a\n"
                    "a      '1234' /[a-z]/ b\n"
                    "b      1 c\n"
                    "       1 d\n"
                    "c      'C'\n"
                    "d      'D'")
        r = {"C": 0, "D": 0}
        for _ in range(1000):
            v = w.generate()
            self.assertRegexpMatches(v, r"^1234[a-z][CD]$")
            r[v[-1]] += 1
        self.assertAlmostEqual(r["C"], 500, delta=50)
        self.assertAlmostEqual(r["D"], 500, delta=50)

    def test_quo1(self):
        w = Grammar("root    '\\\\'")
        g = w.generate()
        self.assertEqual(g, "\\")
        w = Grammar("root    \"\\\\\"")
        g = w.generate()
        self.assertEqual(g, "\\")

    def test_quo2(self):
        w = Grammar("root    '\\''")
        g = w.generate()
        self.assertEqual(g, "'")
        w = Grammar("root    \"\\\"\"")
        g = w.generate()
        self.assertEqual(g, "\"")

    def test_quo3(self):
        w = Grammar("root    '\\'some'")
        g = w.generate()
        self.assertEqual(g, "'some")
        w = Grammar("root    \"\\\"some\"")
        g = w.generate()
        self.assertEqual(g, "\"some")

    def test_quo4(self):
        w = Grammar("root    'some\\''")
        g = w.generate()
        self.assertEqual(g, "some'")
        w = Grammar("root    \"some\\\"\"")
        g = w.generate()
        self.assertEqual(g, "some\"")

    def test_quo5(self):
        # unbalanced parens, end paren is escaped .. should raise
        with self.assertRaises(ParseError):
            Grammar(r"root    '\\\\\\\'")
        with self.assertRaises(ParseError):
            Grammar(r'root    "\\\\\\\"')

    def test_quo6(self):
        w = Grammar(r"root    '\\\\\\\'\\'")
        g = w.generate()
        self.assertEqual(g, "\\\\\\'\\")
        w = Grammar(r'root    "\\\\\\\"\\"')
        g = w.generate()
        self.assertEqual(g, "\\\\\\\"\\")

    def test_quo7(self):
        w = Grammar("root    \"'some\"")
        g = w.generate()
        self.assertEqual(g, "'some")
        w = Grammar("root    '\"some'")
        g = w.generate()
        self.assertEqual(g, "\"some")

    def test_quo8(self):
        w = Grammar("root    \"'\"")
        g = w.generate()
        self.assertEqual(g, "'")
        w = Grammar("root    \"''\"")
        g = w.generate()
        self.assertEqual(g, "''")
        w = Grammar("root    \"'''\"")
        g = w.generate()
        self.assertEqual(g, "'''")
        w = Grammar("root    '\"'")
        g = w.generate()
        self.assertEqual(g, "\"")
        w = Grammar("root    '\"\"'")
        g = w.generate()
        self.assertEqual(g, "\"\"")
        w = Grammar("root    '\"\"\"'")
        g = w.generate()
        self.assertEqual(g, "\"\"\"")

    def test_quo9(self):
        #right: "<h5 id='id824837' onload='chat(\'id705147\',1,\' width=\\\'2pt\\\'\')'>"
        #                                                        ^  -- esc() --   ^
        #wrong: "<h5 id='id824837' onload='chat(\'id705147\',1,\\\' width=\\\'2pt\'\')'>"
        #                                                      ^  -- esc() --   ^
        w = Grammar("root   \"<h5 id='\" id \"' onload='\" esc(func) \"'>\"\n"
                    "id     'id' /[0-9]{6}/\n"
                    "func   \"chat('\" id \"',\" /[0-9]/ \",'\" esc(\" width='2pt'\") \"')\"\n"
                    , esc=lambda x: re.sub(r"('|\\)", r"\\\1", x))
        self.assertRegexpMatches(w.generate(), r"^<h5 id='id[0-9]{6}' onload='chat\(\\'id[0-9]{6}"
                                       r"\\',[0-9],\\' width=\\\\\\'2pt\\\\\\'\\'\)'>$")
        # same grammar with '@id' in chat() instead of 'id'
        w = Grammar("root   \"<h5 id='\" id \"' onload='\" esc(func) \"'>\"\n"
                    "id     'id' /[0-9]{6}/\n"
                    "func   \"chat('\" @id \"',\" /[0-9]/ \",'\" esc(\" width='2pt'\") \"')\"\n"
                    , esc=lambda x: re.sub(r"('|\\)", r"\\\1", x))
        self.assertRegexpMatches(w.generate(), r"^<h5 id='(id[0-9]{6})' onload='chat\(\\'\1"
                                       r"\\',[0-9],\\' width=\\\\\\'2pt\\\\\\'\\'\)'>$")

    def test_func_nest_tracked(self):
        w = Grammar("root   id a(b(@id))\n"
                    "id     'i'\n"
                    , a=lambda x: "a" + x, b=lambda x: "b" + x)
        self.assertEqual(w.generate(), "iabi")

    def test_tracked1(self):
        w = Grammar("root    id '\\n' esc(\"'\" @id \"'\")\n"
                    "id      'id' /[0-9]/",
                    esc=lambda x: re.sub(r"'", "\\'", x))
        defn, use = w.generate().splitlines()
        self.assertRegexpMatches(defn, r"^id[0-9]$")
        self.assertEqual(use, "\\'%s\\'" % defn)

    def test_tracked2(self):
        w = Grammar("root    id '\\n' esc('not', @id)\n"
                    "id      'id' /[0-9]/",
                    esc=lambda x, y: x)
        defn, use = w.generate().splitlines()
        self.assertRegexpMatches(defn, r"^id[0-9]$")
        self.assertEqual(use, "not")

    def test_tracked3(self):
        w = Grammar("root    esc(id) '\\n' @id\n"
                    "id      'id' /[0-9]/",
                    esc=lambda x: "%s\n%s" % (x, "".join("%02x" % ord(c) for c in x)))
        defn, hexn, use = w.generate().splitlines()
        self.assertRegexpMatches(defn, r"^id[0-9]$")
        self.assertEqual("".join("%02x" % ord(c) for c in defn), hexn)
        self.assertEqual(defn, use)

    def test_tracked4(self):
        w = Grammar("root    @id\n"
                    "id      'id' /[0-9]/")
        self.assertRegexpMatches(w.generate(), r"^id[0-9]$")

    def test_tracked5(self):
        w = Grammar("root    esc(id) @id\n"
                    "id      'id' /[0-9]/",
                    esc=lambda x: "")
        self.assertRegexpMatches(w.generate(), r"^id[0-9]$")

    def test_tyson(self):
        w = Grammar('root   /[0-1]{1}/ "]"')
        o = w.generate()
        self.assertIn(o, ["0]", "1]"])

    def test_bin(self):
        w = Grammar("root x'68656c6c6f2c20776f726c6400'")
        self.assertEqual(w.generate(), b"hello, world\0")

    def test_dashname(self):
        w = Grammar("root a-a\n"
                    "a-a 'a'\n")
        self.assertEqual(w.generate(), "a")

    def test_limit(self):
        w = Grammar("root       foo bar\n"
                    "bar {1}    @foo bar\n"
                    "foo        'i0'", limit=10)
        self.assertEqual(len(w.generate()), 10)

    def test_builtin_rndint(self):
        w = Grammar("root       rndint(1,10)")
        self.assertGreaterEqual(int(w.generate()), 1)
        self.assertLessEqual(int(w.generate()), 10)

    def test_builtin_rndflt(self):
        w = Grammar("root       rndflt(1,10)")
        self.assertGreaterEqual(float(w.generate()), 1)
        self.assertLessEqual(float(w.generate()), 10)

    def test_nested_choice_weight(self):
        w = Grammar("root {1000} a\n"
                    "b 9 'b'\n"
                    "a 1 'a'\n"
                    "  1 b")
        o = w.generate()
        a_count = len([c for c in o if c == 'a'])
        b_count = len(o) - a_count
        self.assertAlmostEqual(a_count, b_count, delta=len(o) * 0.2)

    def test_recursive_defn(self):
        with self.assertRaises(IntegrityError):
            Grammar("root root")

    def test_unused_sym(self):
        with self.assertRaisesRegexp(IntegrityError, r'^Unused symbol:'):
            Grammar('root a\n'
                    'a "A"\n'
                    'b "B"')

    def test_unused_cycle(self):
        with self.assertRaises(IntegrityError):
            Grammar('root "A"\n'
                    'a b\n'
                    'b a')


class GrammarImportTests(unittest.TestCase):

    def setUp(self):
        self.tmpd = tempfile.mkdtemp(prefix='gmrtesttmp')
        self.cwd = os.getcwd()
        os.chdir(self.tmpd)

    def tearDown(self):
        os.chdir(self.cwd)
        shutil.rmtree(self.tmpd)

    def test_unused_import(self):
        open('blah.gmr', 'w').close()
        with self.assertRaisesRegexp(IntegrityError, r'^Unused import'):
            w = Grammar("root 'a'\n"
                        "unused import 'blah.gmr'")

    def test_use_before_import(self):
        with self.assertRaisesRegexp(ParseError, r'^Attempt to use symbol from unknown prefix'):
            w = Grammar("root a.b")

    def test_notfound_import(self):
        with self.assertRaisesRegexp(IntegrityError, r'^Could not find imported grammar'):
            w = Grammar("a import ''")

    def test_simple(self):
        with open('a.gmr', 'w') as g:
            g.write('a "A"')
        w = Grammar("b import 'a.gmr'\n"
                    "root b.a")
        self.assertEqual(w.generate(), 'A')

    def test_nested(self):
        with open('a.gmr', 'w') as g:
            g.write('b import "b.gmr"\n'
                    'root a b.a\n'
                    'a "A"')
        with open('b.gmr', 'w') as g:
            g.write('a import "a.gmr"\n'
                    'a @a.a')
        w = Grammar(open('a.gmr'))
        self.assertEqual(w.generate(), "AA")

    def test_recursive_defn(self):
        with open('b.gmr', 'w') as g:
            g.write('b import "b.gmr"\n'
                    'root b.a\n'
                    'a b.a')
        with self.assertRaises(IntegrityError):
            Grammar(open('b.gmr'))

    def test_unused_import_sym(self):
        with open('a.gmr', 'w') as g:
            g.write('a "A"\n'
                    'b "B"')
        Grammar('a import "a.gmr"\n'
                'root a.a')


suite = unittest.TestSuite(unittest.defaultTestLoader.loadTestsFromTestCase(t) for t in (GrammarTests, GrammarImportTests))

