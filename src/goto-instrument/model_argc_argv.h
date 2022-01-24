/*******************************************************************\

Module: Initialize command line arguments

Author: Michael Tautschnig

Date: April 2016

\*******************************************************************/

/// \file
/// Initialize command line arguments

#ifndef CPROVER_GOTO_INSTRUMENT_MODEL_ARGC_ARGV_H
#define CPROVER_GOTO_INSTRUMENT_MODEL_ARGC_ARGV_H

#include <list>
#include <string>

class goto_modelt;
class message_handlert;

bool model_argc_argv(
  goto_modelt &,
  const std::list<std::string> &argv_args,
  bool model_argv,
  message_handlert &);

#define OPT_ARGC_ARGV "(model-argc-argv):(add-cmd-line-arg):"

#define HELP_ARGC_ARGV                                                         \
  " --model-argc-argv <n>        model up to <n> command line arguments\n"     \
  " --add-cmd-line-arg <arg>     add command line argument (may be "           \
  "repeated)\n"

#endif // CPROVER_GOTO_INSTRUMENT_MODEL_ARGC_ARGV_H
