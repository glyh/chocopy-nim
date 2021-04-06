from os import nil
from core/lexer import nil

if os.paramCount() >= 1:
  case os.paramStr(1):
    of "lex":
      echo("Running lexer")
      lexer.run()
    else:
      discard

for i in 0 .. os.paramCount():
  echo(i, "\"", os.paramStr(i), "\"")
