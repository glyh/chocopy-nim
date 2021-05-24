import
  tables, sets, strformat,
  definition

proc buildTree(s_original: seq[Token]) : (Node, int, seq[int]) =
  # Insert ttStart in the beginning, and ttAccept at the end
  var
    tokenStack: seq[Token]  = @[]
    nodeStack: seq[Node]  = @[]
    posCount = 0
    posMap: seq[int] = @[-1]
    s: seq[Token] = @[]
  let s_original = @[Token(ttype: ttLBracket, line: s_original[0].line),
                     Token(ttype: ttStart, line: s_original[0].line)] &
                   s_original &
                   @[Token(ttype: ttAccept),
                     Token(ttype: ttRBracket, line: s_original[^1].line)]
  var needConcat: bool = false
  for i in s_original:
    case i.ttype:
      of ttLBracket:
        if needConcat:
          s.add(Token(ttype: ttOperator, otype: opConcat, line: i.line))
        needConcat = false
      of ttRBracket:
        needConcat = true
      of ttTerminal, ttNonterminal, ttNil, ttAccept, ttStart:
        if needConcat:
          s.add(Token(ttype: ttOperator, otype: opConcat, line: i.line))
        needConcat = true
      of ttOperator:
        if i.otype == opOr:
          needConcat = false
      else: discard
    s.add(i)

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

  for pos in s.low..s.high:
    #echo fmt"Read: {formatToken(i)}"
    let i = s[pos]
    case i.ttype:
      of ttNonterminal, ttTerminal, ttNil, ttStart, ttAccept:
        posCount += 1
        posMap[posCount] = pos
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
    #[
      stdout.write("tokenStack: ")
      for i in tokenStack: stdout.write(formatToken(i) & " ")
      echo""
      stdout.write("nodeStack: ")
      for i in nodeStack: stdout.write(formatToken(i.value) & " ")
      echo""
      echo "------------------------------------------"
    ]#
  (nodeStack.pop(), posCount, posMap)

proc DP(t: Node, r: var SemanticRule) =
  r.followPos = newSeq[HashSet[int]](r.posCount + 1)
  assert t != nil
  if t.left != nil: DP(t.left, r)
  if t.right != nil: DP(t.right, r)

  case t.value.ttype:
    of ttNonterminal, ttTerminal, ttAccept, ttStart:
      t.firstPos = [t.value.pos].toHashSet()
      t.lastPos = [t.value.pos].toHashSet()
      t.nullable = false
    of ttNil:
      t.firstPos = initHashSet[int]()
      t.lastPos = initHashSet[int]()
      t.nullable = true
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
          for i in t.left.lastPos:
            r.followPos[i] = r.followPos[i] + t.right.firstPos
    else: assert false

proc constructLR1Automata(a: var LR1Automata,
                       rules: seq[SemanticRule],
                       map: TableRef[string, int]) =
  const acceptSymbol = Symbol(stype: sAccept)

  proc constructFirstSet(id: int) =
    var r = rules[id]
    r.firstSetStatus = fsCalculating
    case r.firstSetStatus:
      of fsCalculated: return
      of fsCalculating:
        raise newException(
          StackOverflowDefect,
          "Found left recursion at nonterminal: " & r.lhs.value)
      of fsUncalculated:
        var queue: seq[int] = @[]
        for i in r.followPos[1]: queue.add(i)
        var i = 0
        while i <  queue.high:
          let nextToken: Token = r.rhs[r.posMap[queue[i]]]
          case nextToken.ttype:
            of ttNonterminal:
              let rid = map[nextToken.value]
              constructFirstSet(rid)
              r.firstSet = r.firstSet + rules[rid].firstSet
              if acceptSymbol in rules[rid].firstSet:
                for j in r.followPos[nextToken.pos]:
                  queue.add(j)
            of ttTerminal:
              r.firstSet.incl(Symbol(stype: sTerminal, value: nextToken.value))
            of ttAccept: discard
            else:
              raise newException(
                FieldDefect,
                "Invalid Token type for" & formatToken(nextToken))
          i += 1
          if r.expressionTree.nullable:
            r.firstSet.incl(acceptSymbol)
          else:
            r.firstSet.excl(acceptSymbol)
    r.firstSetStatus = fsCalculated

  for i in rules.low..rules.high:
    constructFirstSet(i)

  proc constructClosure(s: var LR1State) =
    var q : seq[LR1Item] = @[]

    proc addItem(id: int, dot: int, sym: Symbol) =
      let newItem: LR1Item = (ruleId: id, dotPos: dot, lookahead: sym)
      if not s.kernal.contains(newItem) and
         not s.closure.contains(newItem):
        q.add(newItem)
        s.closure.incl(newItem)

    for i in s.kernal:
      q.add(i)
    var i = 0
    while i <= q.high:
      let
        cur = q[i]
        r = rules[cur.ruleId]
      if cur.dotPos < r.posCount - 1: # Not accepted yet
        for j in r.followPos[r.posMap[cur.dotPos]]:
          let nextToken: Token = r.rhs[r.posMap[j]]
          case nextToken.ttype:
            of ttNonterminal:
              let nextRuleId = map[nextToken.value]
              for k in r.followPos[1]:
                let lookaheadToken: Token = r.rhs[r.posMap[k]]
                case lookaheadToken.ttype:
                  of ttNonterminal:
                    let id = map[lookaheadToken.value]
                    for i in rules[id].firstSet:
                      addItem(nextRuleId, 1, i)
                  else:
                    addItem(nextRuleId, 1,
                      case lookaheadToken.ttype:
                        of ttAccept:
                          Symbol(stype: sAccept)
                        of ttTerminal:
                          Symbol(stype: sTerminal, value: lookaheadToken.value)
                        else: raise newException(ValueError,
                          "Illed token examined as item."))
            of ttTerminal: discard
            else: assert false

  var kernalMap = newTable[HashSet[LR1Item], int]()
  proc constructGoto(s: var LR1State) =
    var newKernal: Table[Symbol, HashSet[LR1Item]]
    s.goto = newTable[Symbol, int]()

    proc constructWith(i: LR1Item) =
      let r = rules[i.ruleId]
      for j in r.followPos[r.posMap[i.dotPos]]:
        let nextToken = r.rhs[r.posMap[j]]
        let newItem = (ruleId: i.ruleId, dotPos: j, lookahead: i.lookahead)
        case nextToken.ttype:
          of ttAccept: discard
          of ttTerminal:
            let sym = Symbol(stype: sTerminal, value: nextToken.value)
            if not newKernal.hasKey(sym):
              newKernal[sym] = initHashSet[LR1Item]()
            newKernal[sym].incl(newItem)
          of ttNonterminal:
            let sym = Symbol(stype: sNonterminal, id: map[nextToken.value])
            if not newKernal.hasKey(sym):
              newKernal[sym] = initHashSet[LR1Item]()
            newKernal[sym].incl(newItem)
          else: raise newException(ValueError , "Illed token examined as item.")

    for i in s.kernal: constructWith(i)
    for i in s.closure: constructWith(i)
    for k, v in newKernal.mpairs:
      if kernalMap.hasKey(v):
        s.goto[k] = kernalMap[v]
      else:
        a.states.add(LR1State(kernal: v))
        s.goto[k] = a.states.high

  var initialState = LR1State(kernal: @[(ruleId: 0, dotPos: 0, lookahead: acceptSymbol)].toHashSet())
  constructClosure(initialState)
  a.states.add(initialState)
  var i = 0
  while i < a.states.high:
    constructGoto(a.states[i])
    i += 1

proc parseSemanticRule*(rules: var seq[SemanticRule],
                        map: TableRef[string, int]) =
  var id = 1
  for k, r in rules.mpairs:
    r.id = id
    (r.expressionTree, r.posCount, r.posMap) = buildTree(r.rhs)
    DP(r.expressionTree, r)
    r.firstSetStatus = fsUncalculated
    id += 1
  var a: LR1Automata
  constructLR1Automata(a, rules, map)
