from os import nil
from core/lexer import nil
from core/ebnf/ebnf_parse import nil

if os.paramCount() >= 1:
  case os.paramStr(1):
    of "lex":
      lexer.run()
    of "ebnf":
      ebnf_parse.run()

    else:
      discard

#for i in 0 .. os.paramCount():
#  echo(i, "\"", os.paramStr(i), "\"")
