import os, tables, streams, logging, tables, sets, strformat
import definition, lexer, parser
export SymbolType, Symbol, LR1ActionType, LR1Action, LR1State, LR1Automata

var logger = newConsoleLogger()

proc build*(path: string) : LR1Automata =
  var
    tokens = lexer.run(path)
    meetProduction = false
    lhs: Token
    rhs: seq[Token] = @[]
    semanticRules :seq[SemanticRule] = @[]
    nonterminalMap = newTable[string, int]()
    id = 1

  var meetFirstRule = false

  proc tryProduce() =
    if meetProduction:
      meetProduction = false
      if not meetFirstRule:
        meetFirstRule = true
        semanticRules.add(SemanticRule(
          lhs: Token(ttype: ttNonterminal, value: "success"),
          rhs: @[lhs]))
        nonterminalMap["success"] = 0
      semanticRules.add(SemanticRule(lhs: lhs, rhs: rhs))
      nonterminalMap[lhs.value] = id
      id += 1
      rhs = @[]

  for i in tokens:
    case i.ttype:
      of ttProduce:
        meetProduction = true
      of ttNewline:
        tryProduce()
      of ttNonterminal:
        if not meetProduction:
          lhs = i
        else:
          rhs.add(i)
      else:
        rhs.add(i)
  tryProduce()
  parser.run(semanticRules, nonterminalMap)

  #for k, v in semanticRules.pairs():
  #  echo(k, ": " & postOrder(v.expressionTree))

proc run*() =
  # This will directly parse the tokens, treat them as
  # chars rather than stream of tokens

  assert paramCount() >= 3

  #compiler_name ebnf x.ebnf y.in

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
