import os

proc parse(path: string) =
  discard


proc init() =
  discard

proc run*() =
  init()
  if paramCount() >= 2:
    for i in 2 .. paramCount():
      parse(paramStr(i))
