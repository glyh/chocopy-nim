import os
import core/lexer, core/ebnf/ebnf, core/parser

if os.paramCount() >= 1:
  case os.paramStr(1):
    of "lex":
      lexer.run()
    of "ebnf":
      ebnf.run()
    of "parser":
      parser.run()
    of "paramTest":
      echo "paramCount: ", paramCount()
      for i in 0..paramCount():
        echo i, ": ", paramStr(i)
    else:
      discard

#for i in 0 .. os.paramCount():
#  echo(i, "\"", os.paramStr(i), "\"")
