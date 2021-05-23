import os, tables
import definition, lexer, parser

proc build(path: string) =
  var
    tokens = lexer.parse(path)
    meetProduction = false
    lhs: Token
    rhs: seq[Token] = @[]
    semanticRules = newTable[string, SemanticRule]()

  for i in tokens:
    case i.ttype:
      of ttProduce:
        meetProduction = true
      of ttNewline:
        if meetProduction:
          meetProduction = false
          semanticRules[lhs.value] = parser.parseSemanticRule(lhs, rhs)
          rhs = @[]
      of ttNonterminal:
        if not meetProduction:
          lhs = i
        else:
          rhs.add(i)
      else:
        rhs.add(i)
  if meetProduction:
    semanticRules[lhs.value] = parser.parseSemanticRule(lhs, rhs)

proc run*() =
  if paramCount() >= 2:
    for i in 2 .. paramCount():
      build(paramStr(i))
