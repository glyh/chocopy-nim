import os, streams, logging
import lexer, ebnf/ebnf

var logger = newConsoleLogger()

proc parse(path: string) =
  discard

proc run*() =
  if paramCount() >= 3:
    var a = ebnf.build(paramStr(2))
    for i in 3 .. paramCount():
      parse(paramStr(i))
