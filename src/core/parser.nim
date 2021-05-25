import os, streams, logging, strformat, tables, sets
import lexer, ebnf/ebnf

var logger = newConsoleLogger()

proc parse(path: string) =
  discard

proc run*() =
  if paramCount() >= 3:
    var a = ebnf.build(paramStr(2))
    for i in 3 .. paramCount():
      parse(paramStr(i))

proc parseTest*() =
  # This will directly parse the tokens, treat them as
  # chars rather than stream of tokens

  echo paramCount()
  assert paramCount() >= 3

  #compiler_name parseTest x.ebnf y.in
  let a = ebnf.build(paramStr(2))
  echo "LR1 automata built"
  for i in 3 .. paramCount():
    let path = paramStr(i)
    if fileExists(path):
      var s = newFileStream(path, fmRead)
      defer: close(s)
      var c: char = 'x'
      while c != '\0':
        echo "Reading another sequence..."
        var
          curState = 0
          symbolStack: seq[Symbol] = @[]
          stateStack: seq[int] = @[0]
          success: bool = false

        proc tryParse(sym: Symbol): bool =
          #[
            echo "Current state: ", curState
            echo "Current symbol", sym
            echo "SymbolStack: ", symbolStack
            echo "StateStack: ", stateStack
            echo "============================================"
          ]#
          let actions = a.states[curState].action
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
                let rid = action.ruleId
                while stateStack.len() > 0 and
                  a.states[stateStack[^1]].isBody.contains(rid):
                  discard stateStack.pop()
                  discard symbolStack.pop()
                assert a.states[stateStack[^1]].isHead.contains(rid)
                curState = stateStack[^1]
                tryParse(Symbol(stype: sNonterminal, id: rid)) and tryParse(sym)
              of lr1Error:
                logger.log(lvlError, fmt"the LR1 automata have signalled " &
                  "error: {action.message}")
                false
          else:
            false

        while not success:
          c = s.readChar()
          if not (tryParse(
            if not (c in {'\n', '0'}):
              Symbol(stype: sTerminal, value: $c)
            else:
              Symbol(stype: sAccept))): break
        echo success
        while not (c in {'\n', '\0'}):
          c = s.readChar()
    else:
      logger.log(lvlError, fmt"The input file {paramStr(i)} doesn't exists")
