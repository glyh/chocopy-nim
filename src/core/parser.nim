import os, logging, tables, strformat, strutils
import lexer, ebnf/ebnf, definition, ebnf/definition as ebnf_def

var logger = newConsoleLogger()

proc parse*(path: string) =
  var Tokens = lexer.scan(path)
  echo Tokens
  var a = ebnf.build("syntax.ebnf")
  var
    curState = 0
    symbolStack : seq[Symbol] = @[]
    stateStack: seq[int] = @[0]
    success = false
  proc tryParse(sym: Symbol): bool =
    #[
      echo "Current state: ", curState
      echo "Current symbol", sym
      echo "SymbolStack: ", symbolStack
      echo "StateStack: ", stateStack
      echo "============================================"
    ]#
    let actions = a.states[curState].actions
    if actions.hasKey(sym):
      let action = actions[sym]
      case action.lraType:
        of lr1Shift:
          curState = a.states[curState].goto[sym]
          stateStack.add(curState)
          symbolStack.add(sym)
          true
        of lr1Accept:
          success = true
          true
        of lr1Reduce:
          for i in 1..action.tokenCount:
            discard stateStack.pop()
            discard symbolStack.pop()
          curState = stateStack[^1]
          tryParse(action.output) and tryParse(sym)
        of lr1Error:
          logger.log(lvlError, fmt"the LR1 automata have signalled " &
            "error: {action.message}")
          false
    else: false
  for i in Tokens:
    let next =
      case i.ctype:
        of ctInt: "INTEGER"
        of ctString: "STRING"
        of ctPreserved, ctSymbol: i.vstr
        of ctId: "ID"
        of ctIndent: "INDENT"
        of ctDedent: "DEDENT"
        of ctNewLine: "NEWLINE"
        else: raise newException(FieldDefect, "Impossible")
    if tryParse(ebnf_def.Symbol(stype: sTerminal, value: next)):
      echo fmt"Parsing {next} with {i}!"
    else:
      echo fmt"Failed at {next} with {i}!"
      return

  if not tryParse(ebnf_def.Symbol(stype: sAccept)):
    echo "Failed to accept!"

proc run*() =
  if paramCount() >= 3:
    var a = ebnf.build(paramStr(2))
    for i in 3 .. paramCount():
      parse(paramStr(i))
