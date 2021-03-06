********************************************
:mod:`alf.debug` ALF Debugging Library
********************************************

.. module:: alf.debug
    :synopsis: Library of target execution and fault monitoring helper functions.

This module provides a set of target execution and debugging helper functions, useful
for fault detection and analysis in fuzzer development.

Callbacks
=========

Most of the :func:`run` family of functions defined in this module take an optional callback
and callback arguments. If a callback is given, it is called immediately after the target is launched.
These are typically used to interact with the target in some
way which can't be done using command line parameters or file I/O. They are expected to report
back a status using one of the :ref:`CB_CONSTANTS` defined in this module. The documentation for :class:`alf.debug.TargetPid` describes how a callback can get a handle
to the target using the process identifier (PID).

Functions
=========

.. autofunction:: alf.debug.attach_with_windbg

.. autofunction:: alf.debug.reduce_timeout_with_windbg

.. autofunction:: alf.debug.run

.. autofunction:: alf.debug.run_with_gdb

.. autofunction:: alf.debug.run_with_qemu

.. autofunction:: alf.debug.run_with_windbg

.. autofunction:: alf.debug.trace_memory_usage_with_windbg

Classes
=======

.. autoclass:: alf.debug.TargetPid

.. _CB_CONSTANTS:

Constants
=========

.. data:: alf.debug.CB_PASS

   Callback returned successfully. No effect is had on the result of the calling function.

.. data:: alf.debug.CB_FAIL

   Callback detected that target crashed/failed. The calling function will report a failure
   in the target, even if one is not detected otherwise. This means that :data:`~alf.debug.NOT_AN_EXCEPTION`
   results will be elevated to :data:`~alf.debug.UNKNOWN`.

.. data:: alf.debug.CB_HANG

   Callback detected that target is hung/unresponsive. The calling function will report
   a result with classification :data:`~alf.debug.TIMEOUT`, even if the target would have generated
   another classification otherwise.

.. data:: alf.debug.CB_ERROR

   Callback (not target) failed. An error will be reported to the ALF server for review by
   the project owner and ALF admins.

.. data:: alf.debug.EXCESS_MEMORY_USAGE

   Application exceeded the defined memory limit

.. data:: alf.debug.EXPLOITABLE

   Defect can be used to achieve arbitrary code execution

.. data:: alf.debug.NOT_AN_EXCEPTION

   Application did exit but encountered issues

.. data:: alf.debug.PROBABLY_EXPLOITABLE

   Defect can likely be used to achieve arbitrary code execution

.. data:: alf.debug.PROBABLY_NOT_EXPLOITABLE

   Unexpected application termination usually due to a read access violation

.. data:: alf.debug.TIMEOUT

   Application did not exit within given time. Usually stuck in a loop

.. data:: alf.debug.UNKNOWN

   Unexpected application termination exploitability can't be automatically determined

.. data:: alf.debug.DEFAULT_TIMEOUT

   Default time limit for `~alf.debug.run()` and similar functions which take a ``timeout`` argument. (60s)

Examples
========

These examples are ways in which, during an iteration run by
:meth:`~alf.Fuzzer.do_iteration`, control might be
exercised of the environment and the subject being fuzzed.  The details vary because of the
many ways a fuzz subject might demand to be run or used: as a single program, as a continuaously
running process, or, in the biggest case, as a collection of cooperating processes
which may depend on an external resource.   The ALF framework provides facilities to 
run and monitor parts of such a subject with and without a debugger.  A plugin designer
should provide debuggable builds of executables (if required), and must take care to 
depend only on extraneous resources which are or can be made available for automated testing.

The example programs ``my_something`` below are purely imaginary.  Resemblance to real
programs living or dead is a coincidence.

Example 1 : use :func:`run` on QNX to stop any ``my_runner`` processes from a previous iteration::

   my_runner = 'my_runner'
   (num_slain, _, _) = alf.debug.run(['/bin/slay', '-f', my_runner])
   print 'Slayed %d previously running %s processes.' % (num_slain, my_runner)

Example 2 : use :func:`run` on Unix to create a test user if necessary::

   user_name = 'fuzz_tester'
   if os.path.expanduser('~%s'%user_name).startswith('~'):
       (exit_code, _, _) = alf.debug.run(['useradd', '-c "test user"', user_name])
       if exit_code != 0:
           print "Can't create user %s." % user_name

Example 3 : use :func:`~alf.debug.run_with_windbg` to fuzz ``my_prog.exe`` from the project install directory
with arguments including a mutated file::

   TOOL = 'my_prog.exe'
   command = os.path.join(self.project_root, TOOL)
   (exit_code, result) = alf.debug.run_with_windbg([command, '--quiet', '--input=%s'%mutation_fn])
   if result.classification != alf.debug.NOT_AN_EXCEPTION:
       return result

Example 4 : use :func:`~alf.debug.run_with_gdb` to run a web service program ``my_server`` under the debugger
and use callback parameter to interact with it::

   import urllib
   my_server = os.path.join(self.project_root, 'my_server')
   port = 2000
   url = 'http://localhost:%d/do?something' % port
   from_server = []
   (exit_code, result) = alf.debug.run_with_gdb(
       target_cmd = [my_server, '--bindaddr=localhost', '--port=%d'%port],
       callback = lambda:from_server.extend(urllib.urlopen(url))
   )
   # check got something
   if not from_server:
       result.classification = alf.debug.UNKNOWN

   # return exceptional result
   if result.classification != alf.debug.NOT_AN_EXCEPTION:
       return result

Example 4b : on Windows the above example would work with ``gdb``, or with ``cdb``
by calling  :func:`~alf.debug.run_with_windbg` instead of  :func:`~alf.debug.run_with_gdb`.

Example 5 : using :func:`~alf.debug.run` launch a test case ``my_prog.exe`` without the debugger
and return a result on failure::

   TOOL = 'my_prog.exe'
   command = os.path.join(self.project_root, TOOL)
   pids = []
   (exit_code, _, was_timeout) = alf.debug.run(
       target_cmd=[command, mutation_fn],
       callback=lambda t:pids.append(t.pid),
       callback_args=[alf.debug.TargetPid()]
   )
   if exit_code != 0 or was_timeout:
       (pid,) = pids

       # extract a stack trace from a log file?
       stack_trace = _my_stack_trace(pid)

       result = alf.FuzzResult(alf.debug.UNKNOWN, '[%s]: exit(%s).' % (pid, exit_code), stack_trace)
       return result


Example 6 : for using :func:`~alf.debug.run_with_qemu` for ``'ntoarm'`` emulator::

   command = 'my_ntoarm_exe'
   (exit_code, result) = alf.debug.run_with_qemu([command, "--input=%s" % mutation_fn], input_files=[mutation_fn])
   if result.classification != alf.debug.NOT_AN_EXCEPTION:
       return result
