from os import nil
from core/lexer import nil
from core/ebnf/ebnf import nil

if os.paramCount() >= 1:
  case os.paramStr(1):
    of "lex":
      lexer.run()
    of "ebnf":
      ebnf.run()
    else:
      discard

#for i in 0 .. os.paramCount():
#  echo(i, "\"", os.paramStr(i), "\"")
