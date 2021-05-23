#null to be implemented
import tables, sets, strformat
import definition

func buildTree(s_original: seq[Token]) : (Node, int) =
  var
    tokenStack: seq[Token]  = @[]
    nodeStack: seq[Node]  = @[]
    posCount = 0

  var s: seq[Token] = @[Token(ttype: ttLBracket, line: s_original[0].line)]
  var needConcat: bool = false
  for i in s_original:
    case i.ttype:
      of ttLBracket:
        if needConcat:
          s.add(Token(ttype: ttOperator, otype: opConcat, line: i.line))
        needConcat = false
      of ttRBracket:
        needConcat = true
      of ttTerminal, ttNonterminal:
        if needConcat:
          s.add(Token(ttype: ttOperator, otype: opConcat, line: i.line))
        needConcat = true
      of ttOperator:
        if i.otype == opOr:
          needConcat = false
      else: discard
    s.add(i)
  s.add(Token(ttype: ttRBracket, line: s_original[^1].line))

  proc eliminate() =
    let
      token = tokenStack.pop()
      tr = nodeStack.pop()
    assert token.ttype == ttOperator
    if opUnary[token.otype]:
      nodeStack.add(Node(left: tr, right: nil, value: token))
    else:
      let tl = nodeStack.pop()
      nodeStack.add(Node(left: tl, right: tr, value: token))

  for i in s:
    case i.ttype:
      of ttNonterminal, ttTerminal:
        posCount += 1
        var tFix = i
        tFix.pos = posCount
        nodeStack.add(Node(left: nil, right: nil, value: tFix))
      of ttOperator:
        let pi: int = opPrecedence[i.otype]
        while tokenStack.len() != 0 and tokenStack[^1].ttype == ttOperator:
          let plas: int = opPrecedence[tokenStack[^1].otype]
          if plas >= pi: # We only have left associative operators
            eliminate()
          else: break
        tokenStack.add(i)
      of ttLBracket:
        tokenStack.add(i)
      of ttRBracket:
        while tokenStack[^1].ttype == ttOperator:
          eliminate()
        discard tokenStack.pop()
      else: assert false
  return (nodeStack.pop(), posCount)

proc DP(t: Node, r: var SemanticRule) =
  r.followPos = newSeq[HashSet[int]](r.posCount + 1)
  assert t != nil
  if t.left != nil: DP(t.left, r)
  if t.right != nil: DP(t.right, r)

  case t.value.ttype:
    of ttNonterminal, ttTerminal:
      t.firstPos = [t.value.pos].toHashSet()
      t.lastPos = [t.value.pos].toHashSet()
      t.nullable = false
    of ttOperator:
      case t.value.otype:
        of opOr:
          t.firstPos = t.left.firstPos + t.right.firstPos
          t.lastPos = t.left.lastPos + t.right.lastPos
          t.nullable = t.left.nullable or t.right.nullable
        of opOptional:
          t.firstPos = t.left.firstPos
          t.lastPos = t.left.lastPos
          t.nullable = true
        of opKleen:
          t.firstPos = t.left.firstPos
          t.lastPos = t.left.lastPos
          t.nullable = true
          for i in t.lastPos:
            r.followPos[i] = r.followPos[i] + t.firstPos
        of opPositive:
          t.firstPos = t.left.firstPos
          t.lastPos = t.left.lastPos
          t.nullable = t.left.nullable
          for i in t.lastPos:
            r.followPos[i] = r.followPos[i] + t.firstPos
        of opConcat:
          t.firstPos = t.left.firstPos
          if t.left.nullable: t.firstPos = t.firstPos + t.right.firstPos
          t.lastPos = t.right.lastPos
          if t.right.nullable: t.lastPos = t.lastPos + t.left.lastPos
          t.nullable = t.left.nullable and t.right.nullable
    else: assert false

proc parseSemanticRule*(lhs: Token, rhs : seq[Token]) : SemanticRule =
  echo fmt"parse {formatToken(lhs)}"
  #echo ""
  var r = SemanticRule(lhs: lhs, rhs: rhs)
  (r.expressionTree, r.posCount) = buildTree(rhs)
  #echo "postOrder:"
  #postOrder(r.expressionTree)
  #echo""
  DP(r.expressionTree, r)
  return r

#[
proc generateFirstSet(r : SemanticRule) =
  discard

  proc generate(tokens: seq[Token]) : seq[LR1Item] =
    var rules: seq[SemanticRule] = @[]
    var rule: SemanticRule
    var meetProduction = false
    for i in tokens:
      if i.ttype == ttNewline:
        add(rules, rule)
        meetProduction = false
      elif meetProduction:
        add(rule.rhs, i)
      elif i.ttype == ttProduce:
        meetProduction = true
      else:
        rule.lhs = i
    for i in rules:
      generateFirstSet(i)
    return @[]
]#
