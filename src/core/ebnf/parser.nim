import
  tables, sets, strformat, os,
  definition

proc buildTree(s_original: var seq[Token]) : (Node, int, seq[int]) =
  # Insert ttStart in the beginning, and ttAccept at the end
  var
    tokenStack: seq[Token]  = @[]
    nodeStack: seq[Node]  = @[]
    posCount = 0
    posMap: seq[int] = @[-1]
    s: seq[Token] = @[]
  var needConcat: bool = false
  for i in
    @[Token(ttype: ttLBracket, line: s_original[0].line),
      Token(ttype: ttStart, line: s_original[0].line),
      Token(ttype: ttLBracket, line: s_original[0].line)] &
    s_original &
    @[Token(ttype: ttRBracket, line: s_original[^1].line),
      Token(ttype: ttAccept),
      Token(ttype: ttRBracket, line: s_original[^1].line)] :
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

  for pos, i in s.mpairs:
    case i.ttype:
      of ttNonterminal, ttTerminal, ttNil, ttStart, ttAccept:
        posCount += 1
        posMap.add(pos)
        i.pos = posCount
        nodeStack.add(Node(left: nil, right: nil, value: i))
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
  s_original = s
  (nodeStack.pop(), posCount, posMap)

proc DP(t: Node, r: var SemanticRule) =
  assert t != nil
  if t.left != nil: DP(t.left, r)
  if t.right != nil: DP(t.right, r)

  case t.value.ttype:
    of ttNonterminal, ttTerminal:
      t.firstPos = [t.value.pos].toHashSet()
      t.lastPos = [t.value.pos].toHashSet()
      t.nullable = false
    of ttAccept, ttStart:
      t.firstPos = [t.value.pos].toHashSet()
      t.lastPos = [t.value.pos].toHashSet()
      t.nullable = true
      #if t.value.ttype == ttStart:
      #  echo "-----", t.firstPos," ",  t.lastPos, " ", t.nullable
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
    #echo "constructFirstSet: ", rules[id].lhs.value
    var r = rules[id]
    case r.firstSetStatus:
      of fsCalculated: return
      of fsCalculating:
        raise newException(
          StackOverflowDefect,
          "Found left recursion at nonterminal: " & r.lhs.value)
      of fsUncalculated:
        r.firstSetStatus = fsCalculating
        var queue: seq[int] = @[]
        for i in r.followPos[1]: queue.add(i)
        var i = 0
        while i <= queue.high:
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
                "Invalid Token type for " & $(nextToken))
          i += 1
          if r.expressionTree.nullable:
            r.firstSet.incl(acceptSymbol)
          else:
            r.firstSet.excl(acceptSymbol)
    r.firstSetStatus = fsCalculated

  for i in rules.low..rules.high:
    constructFirstSet(i)
  #echo "FirstSet constructed"

  proc constructClosure(s: var LR1State,
                       rules: seq[SemanticRule],
                       map: TableRef[string, int]) =
    if s.closure.len != 0: return
    var q: seq[LR1Item] = @[]

    proc addItem(
      s: var LR1State, q: var seq[LR1Item], id: int, dot: int, sym: Symbol) =
      let newItem: LR1Item = (ruleId: id, dotPos: dot, lookahead: sym)
      if not s.kernal.contains(newItem) and not s.closure.contains(newItem):
        q.add(newItem)
        s.closure.incl(newItem)

    #echo fmt"Construct closure for: {s.kernal}"
    s.closure = initHashSet[LR1Item]()
    for i in s.kernal:
      q.add(i)
    var i = 0
    while i <= q.high:
      let
        cur = q[i]
        r = rules[cur.ruleId]
      #A -> alpha dot B beta, a
      if cur.dotPos < r.posCount - 1: # Not accepted yet
        for j in r.followPos[cur.dotPos]: # j is the position of B
          let nextToken: Token = r.rhs[r.posMap[j]]
          case nextToken.ttype:
            of ttNonterminal:
              let nextRuleId = map[nextToken.value]
              for k in r.followPos[j]: # k is the position of beta
                let lookaheadToken: Token = r.rhs[r.posMap[k]]
                case lookaheadToken.ttype:
                  of ttNonterminal:
                    let id = map[lookaheadToken.value]
                    for i in rules[id].firstSet:
                      addItem(s, q, nextRuleId, 1, i)
                  else:
                    addItem(s, q, nextRuleId, 1,
                      case lookaheadToken.ttype:
                        of ttAccept:
                          cur.lookahead
                        of ttTerminal:
                          Symbol(stype: sTerminal, value: lookaheadToken.value)
                        else: raise newException(ValueError,
                          "Illed token examined as item."))
            of ttTerminal, ttAccept: discard
            else: assert false
      i += 1
    #echo fmt"got: {s.closure}"

  var kernalMap = newTable[HashSet[LR1Item], int]()
  proc constructGoto(a: var LR1Automata, s_pos: int) =
    var
      s = a.states[s_pos]
      newKernal: Table[Symbol, HashSet[LR1Item]]

    s.goto = newTable[Symbol, int]()
    kernalMap[s.kernal] = s_pos

    for i in s.kernal + s.closure:
      let r = rules[i.ruleId]
      for j in r.followPos[i.dotPos]:
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

    for k, v in newKernal.pairs:
      if kernalMap.hasKey(v):
        s.goto[k] = kernalMap[v]
      else:
        a.states.add(LR1State(kernal: v))
        s.goto[k] = a.states.high
        kernalMap[v] = a.states.high

  proc constructAction(curState: var LR1State) =
    proc tryAddAction(state: var LR1State, sym: Symbol, action: LR1Action) =
      if state.action.hasKey(sym):
        let actionAlready = state.action[sym]
        if not (actionAlready == action):
          raise newException(ValueError,
            fmt"Conflict in LR(1) dectected between {actionAlready} " &
            "and {action} for transition {sym} in state {state.kernal}")
      else:
        state.action[sym] = action
    curState.action = newTable[Symbol, LR1Action]()
    for k in (curState.kernal + curState.closure):
      let r = rules[k.ruleId]
      for j in r.followPos[k.dotPos]:
        let tok = r.rhs[r.posMap[j]]
        case tok.ttype:
          of ttTerminal:
            tryAddAction(
              curState,
              Symbol(stype: sTerminal, value: tok.value),
              LR1Action(lraType: lr1Shift))
          of ttNonterminal:
            tryAddAction(
              curState,
              Symbol(stype: sNonterminal, id: map[tok.value]),
              LR1Action(lraType: lr1Shift))
          of ttAccept:
            tryAddAction(
              curState,
              k.lookahead,
              if k.ruleId == 0:
                LR1Action(lraType: lr1Accept)
              else:
                LR1Action(lraType: lr1Reduce, ruleId: k.ruleId))
          else: assert(tok.ttype == ttNonterminal)

  proc constructMark(curState: LR1State) =
    curState.isHead = initHashSet[int]()
    curState.isBody = initHashSet[int]()
    for i in (curState.kernal + curState.closure):
      if i.dotPos == 1:
        curState.isHead.incl(i.ruleId)
      else:
        curState.isBody.incl(i.ruleId)

  var initialState = LR1State(
    kernal: [(ruleId: 0, dotPos: 1, lookahead: acceptSymbol)].toHashSet())
  a.states.add(initialState)
  var i = 0
  while i <= a.states.high:
    var curState = a.states[i]
    constructClosure(curState, rules, map)
    constructGoto(a, i)
    constructMark(curState)
    constructAction(curState)
    i += 1

proc run*(rules: var seq[SemanticRule],
          map: TableRef[string, int]) : LR1Automata =
  var id = 1
  for r in rules.mitems:
    r.id = id
    (r.expressionTree, r.posCount, r.posMap) = buildTree(r.rhs)
    r.followPos = newSeq[HashSet[int]](r.posCount + 1)
    DP(r.expressionTree, r)
    r.firstSetStatus = fsUncalculated
    #-------------------------
    #[
      stdout.write(formatToken(r.lhs), " -> ")
      for i in r.rhs:
        stdout.write(formatToken(i), " ")
      echo""
      echo fmt"posCount: {r.posCount}, size of posMap: {r.posMap.len()}"
      for i in 1..r.posCount:
        stdout.write fmt"{i}: {r.followPos[i]}:"
        for j in r.followPos[i]:
          stdout.write(r.rhs[r.posMap[j]].formatToken(), " ")
        echo""
      id += 1
      echo "============================"
    ]#
    #-------------------------
  var a: LR1Automata
  constructLR1Automata(a, rules, map)
  for k, s in a.states.pairs:
    echo k, ": ", s.kernal
  for id, s in a.states.pairs:
    for k, v in s.goto:
      echo fmt"F[{id}][{k}] = {v}"
    for k,v in s.action:
      echo fmt"Action[{id}][{k}] = {v}"
    echo fmt"IsHead[{id}] = {s.isHead}"
  a
