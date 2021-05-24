import
  os, tables,
  definition, lexer, parser
export definition

proc build(path: string) =
  var
    tokens = lexer.parse(path)
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
    id += 1
  tryProduce()
  parseSemanticRule(semanticRules, nonterminalMap)

  for k, v in semanticRules.pairs():
    echo(k, ": " & postOrder(v.expressionTree))

proc run*() =
  if paramCount() >= 2:
    for i in 2 .. paramCount():
      build(paramStr(i))
