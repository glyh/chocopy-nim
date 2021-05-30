import
  tables, sets, strformat, os, sequtils, sugar,
  definition

proc buildTree(s_original: var seq[Token]) : Node =
  # Insert ttStart in the beginning, and ttAccept at the end
  var
    tokenStack: seq[Token]  = @[]
    nodeStack: seq[Node]  = @[]
    s: seq[Token] = @[]
  var needConcat: bool = false
  for i in
    @[Token(ttype: ttLBracket, line: s_original[0].line)] &
      s_original &
    @[Token(ttype: ttRBracket, line: s_original[^1].line)] :
    case i.ttype:
      of ttLBracket:
        if needConcat:
          s.add(Token(ttype: ttOperator, otype: opConcat, line: i.line))
        needConcat = false
      of ttRBracket:
        needConcat = true
      of ttTerminal, ttNonterminal, ttNil:
        if needConcat:
          s.add(Token(ttype: ttOperator, otype: opConcat, line: i.line))
        needConcat = true
      of ttOperator:
        if i.otype == opOr:
          needConcat = false
      else: discard
    s.add(i)

  var id = 0
  proc eliminate() =
    let
      token = tokenStack.pop()
      tr = nodeStack.pop()
    assert token.ttype == ttOperator
    if opUnary[token.otype]:
      nodeStack.add(Node(left: tr, right: nil, value: token, id: id))
    else:
      let tl = nodeStack.pop()
      nodeStack.add(Node(left: tl, right: tr, value: token, id: id))
    id += 1

  for pos, i in s.mpairs:
    case i.ttype:
      of ttNonterminal, ttTerminal, ttNil, ttAccept:
        nodeStack.add(Node(left: nil, right: nil, value: i, id: id))
        id += 1
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
  nodeStack.pop()

# DP takes over the desugar job
proc DP(
  t: var Node,
  tag: string,
  rulesDesugared: var TableRef[string, SemanticRuleDesugared]) =
  assert t != nil
  if t.left != nil: DP(t.left, tag, rulesDesugared)
  if t.right != nil: DP(t.right, tag, rulesDesugared)

  let idCurrent = tag & $t.id
  case t.value.ttype:
    of ttNonterminal, ttTerminal, ttNil:
      rulesDesugared[idCurrent] = SemanticRuleDesugared(
        rhs: @[@[
          case t.value.ttype
            of ttNonterminal:
              Symbol(stype: sNonterminal, value: t.value.value)
            of ttTerminal:
              Symbol(stype: sTerminal, value: t.value.value)
            of ttNil:
              Symbol(stype: sNil)
            else:
              raise newException(FieldDefect, "Impossible")]],
        nullable: t.value.ttype == ttNil)
      t.meet = rnNone
    of ttOperator:
      if t.right == nil:
        t.meet = t.left.meet
      else:
        t.meet = max(t.left.meet, t.right.meet)
      let
        idLeft = tag & $t.left.id
        idRight =
          if t.right == nil: ""
          else: tag & $t.right.id
        rLeft = rulesDesugared[idLeft]
        rRight = if idRight == "": rLeft else: rulesDesugared[idRight]
      case t.value.otype:
        of opOr:
          if t.meet == rnRewrite:
            rulesDesugared[idCurrent] = SemanticRuleDesugared(
              rhs: @[@[Symbol(stype: sNonterminal, value: idLeft)],
                     @[Symbol(stype: sNonterminal, value: idRight)]],
              nullable: rLeft.nullable or rRight.nullable)
          else:
            rulesDesugared[idCurrent] = SemanticRuleDesugared(
              rhs: rLeft.rhs & rRight.rhs,
              nullable: rLeft.nullable or rRight.nullable)
            rulesDesugared.del(idLeft)
            rulesDesugared.del(idRight)
          t.meet = rnMeetOr
        of opOptional:
          if t.meet == rnRewrite:
            rulesDesugared[idCurrent] = SemanticRuleDesugared(
              rhs: @[@[Symbol(stype: sNonterminal, value: idLeft)],
                   @[Symbol(stype: sNil)]],
              nullable: true)
          else:
            rulesDesugared[idCurrent] = SemanticRuleDesugared(
              rhs: rLeft.rhs & @[Symbol(stype: sNil)],
              nullable: true)
            rulesDesugared.del(idLeft)
            t.meet = rnMeetOr
        of opKleen:
          if t.meet <= rnMeetConcat:
            rulesDesugared[idCurrent] = SemanticRuleDesugared(
              rhs: @[
                @[Symbol(stype: sNil)],
                rLeft.rhs[0] & @[Symbol(stype: sNonterminal, value: idCurrent)]
              ],
              nullable: true)
            rulesDesugared.del(idLeft)
          else:
            rulesDesugared[idCurrent] = SemanticRuleDesugared(
              rhs: @[
                @[Symbol(stype: sNil)],
                @[Symbol(stype: sNonterminal, value: idLeft),
                  Symbol(stype: sNonterminal, value: idCurrent)]],
              nullable: true)
          t.meet = rnRewrite
        of opPositive:
          if t.meet <= rnMeetConcat:
            rulesDesugared[idCurrent] = SemanticRuleDesugared(
              rhs: @[
                rLeft.rhs[0],
                rLeft.rhs[0] & @[Symbol(stype: sNonterminal, value: idCurrent)]
              ],
              nullable: true)
            rulesDesugared.del(idLeft)
          else:
            rulesDesugared[idCurrent] = SemanticRuleDesugared(
              rhs: @[
                @[Symbol(stype: sNonterminal, value: idLeft)],
                @[Symbol(stype: sNonterminal, value: idLeft),
                  Symbol(stype: sNonterminal, value: idCurrent)]],
              nullable: true)
          t.meet = rnRewrite
        of opConcat:
          if t.meet in {rnNone, rnMeetConcat}:
            let rRight = rulesDesugared[idRight]
            assert rRight.rhs.len != 0
            if rLeft.rhs.len == 1 and rRight.rhs.len == 1:
              rulesDesugared[idCurrent] = SemanticRuleDesugared(
                rhs: @[rLeft.rhs[0] & rRight.rhs[0]],
                nullable: rLeft.nullable and rRight.nullable)
              rulesDesugared.del(idLeft)
              rulesDesugared.del(idRight)
            else:
              let postfix =
                if rRight.rhs.len == 1: rRight.rhs[0]
                else: @[Symbol(stype: sNonterminal, value: idRight)]
              rulesDesugared[idCurrent] = SemanticRuleDesugared(
                rhs: rLeft.rhs.map(x => (x & postfix)),
                nullable: rLeft.nullable and rRight.nullable)
              rulesDesugared.del(idLeft)
              if rRight.rhs.len == 1: rulesDesugared.del(idRight)
          else:
            rulesDesugared[idCurrent] = SemanticRuleDesugared(
              rhs: @[
                @[Symbol(stype: sNonterminal, value: idLeft),
                  Symbol(stype: sNonterminal, value: idRight)]],
              nullable: rLeft.nullable and rRight.nullable)
          t.meet = rnMeetConcat
    else: assert false

proc constructLR1Automata(
  a: var LR1Automata,
  rulesDesugared: TableRef[string, SemanticRuleDesugared]) =
  const acceptSymbol = Symbol(stype: sAccept)

  func lookAhead(r: seq[Symbol], pos: int): (Symbol, int) =
    # lookAhead wil not return sNil for you
    var pos = pos + 1
    while pos <= r.high and r[pos].stype == sNil:
      pos += 1
    ((if pos > r.high:
      acceptSymbol
    else:
      r[pos]),
    pos)

  proc constructFirstSet(nonTerminal: string) =
    var r = rulesDesugared[nonTerminal]
    case r.firstSetStatus:
      of fsCalculated: return
      of fsCalculating:
        raise newException(
          StackOverflowDefect,
          "Found left recursion at nonterminal: " & nonTerminal)
      of fsUncalculated:
        r.firstSetStatus = fsCalculating
        for i in r.rhs:
          var (sym, j) = lookAhead(i, -1)
          # sNil is taken care of by lookAhead
          while sym.stype == sNonterminal and
                rulesDesugared[sym.value].nullable:
            constructFirstSet(sym.value);
            r.firstSet = r.firstSet + rulesDesugared[sym.value].firstSet
            (sym, j) = lookAhead(i, j)
          case sym.stype:
            of sTerminal:
              r.firstSet.incl(sym)
            of sNonterminal:
              constructFirstSet(sym.value)
              r.firstSet = r.firstSet + rulesDesugared[sym.value].firstSet
            of sNil: raise newException(FieldDefect, "Impossible value")
            of sAccept: discard
        r.firstSetStatus = fsCalculated

  proc constructClosure(s: var LR1State,
                       map: TableRef[string, int]) =
    if s.closure.len != 0: return
    var q: seq[LR1Item] = @[]

    proc addItem(
      s: var LR1State,
      q: var seq[LR1Item],
      id: string,
      dot: tuple[p: int, q: int],
      sym: Symbol) =
      let newItem: LR1Item = (rule: id, dot: dot, lookahead: sym)
      if not s.kernal.contains(newItem) and not s.closure.contains(newItem):
        q.add(newItem)
        s.closure.incl(newItem)

    s.closure = initHashSet[LR1Item]()
    for i in s.kernal: q.add(i)
    var i = q.low
    while i <= q.high:
      let
        cur = q[i]
        (caseId, pos) = cur.dot
        r = rulesDesugared[cur.rule].rhs[caseId]
        (B, BPos) = lookAhead(r, pos)
      # A -> alpha dot B beta, a
      if B.stype == sNonterminal:
        # A can be written in "alpha B beta", where B is not nil
        # for next in rulesDesugared[nextSymbol.value].
        var
          (betaX, betaPos) = lookAhead(r, BPos)
          betaFirstSet = initHashSet[Symbol]()
          # Actually is the firstSet of "beta a"
        # beta's first symbol
        while betaX.stype == sNonterminal:
          let rBetaX = rulesDesugared[betaX.value]
          if not rBetaX.nullable: break
          betaFirstSet = betaFirstSet + rBetaX.firstSet
          (betaX, betaPos) = lookAhead(r, betaPos)
        case betaX.stype:
          of sNonterminal:
            let rBetaX = rulesDesugared[betaX.value]
            betaFirstSet = betaFirstSet + rBetaX.firstSet
          of sTerminal:
            betaFirstSet.incl(betaX)
          of sAccept: # everything read up
            betaFirstSet.incl(cur.lookahead)
          of sNil: raise newException(FieldDefect, "Impossible value")
        for i in rulesDesugared[B.value].rhs.low ..
                 rulesDesugared[B.value].rhs.high:
          for j in betaFirstSet:
            addItem(s, q, B.value, (i, -1), j)
      i += 1

  var kernalMap = newTable[HashSet[LR1Item], int]()
  proc constructGoto(a: var LR1Automata, s_pos: int) =
    var
      s = a.states[s_pos]
      newKernal: Table[Symbol, HashSet[LR1Item]]
    s.goto = newTable[Symbol, int]()
    kernalMap[s.kernal] = s_pos

    for i in s.kernal + s.closure:
      let
        (symNext, posNext) =
          lookAhead(rulesDesugared[i.rule].rhs[i.dot.p], i.dot.q)
        newItem = (rule: i.rule,
                   dot: (i.dot.p, posNext),
                   lookahead: i.lookahead)
      if symNext.stype in {sTerminal, sNonterminal}:
        if not newKernal.hasKey(symNext):
          newKernal[symNext] = initHashSet[LR1Item]()
        newKernal[symNext].incl(newItem)
    for k, v in newKernal.pairs:
      if kernalMap.hasKey(v):
        s.goto[k] = kernalMap[v]
      else:
        a.states.add(LR1State(kernal: v))
        s.goto[k] = a.states.high
        kernalMap[v] = a.states.high

  proc constructAction(curState: var LR1State, rulesMap: TableRef[string, int]) =
    proc tryAddAction(state: var LR1State, sym: Symbol, action: LR1Action) =
      echo fmt"try add F[{state.kernal}, {sym}] <- {action}"
      if state.actions.hasKey(sym):
        let actionAlready = state.actions[sym]
        if not (actionAlready == action):
          raise newException(ValueError,
            fmt"Conflict in LR(1) dectected between {actionAlready} " &
            "and {action} for transition {sym} in state {state.kernal}")
      else:
        state.actions[sym] = action
    curState.actions = newTable[Symbol, LR1Action]()
    for i in (curState.kernal + curState.closure):
      let
        r = rulesDesugared[i.rule]
        (symNext, _) = lookAhead(r.rhs[i.dot.p], i.dot.q)
      tryAddAction(
        curState,
        if symNext.stype == sAccept:
          i.lookahead
        else:
          symNext,
        if symNext.stype in {sTerminal, sNonterminal}:
          LR1Action(lraType: lr1Shift)
        elif i.rule == "success":
          LR1Action(lraType: lr1Accept)
        else:
          LR1Action(lraType: lr1Reduce,
                    tokenCount: r.rhs[i.dot.p].len,
                    output: Symbol(stype: sNonterminal, value: i.rule)))
  var
    initialState = LR1State(
      kernal:
        [(rule: "success", dot: (0, -1), lookahead: acceptSymbol)].toHashSet())
    i = 0
    map =  newTable[string, int]()
    p = 0
  for k in rulesDesugared.keys:
    map[k] = p
    constructFirstSet(k)
    p += 1
  a.states.add(initialState)
  while i <= a.states.high:
    var curState = a.states[i]
    constructClosure(curState, map)
    constructGoto(a, i)
    constructAction(curState, map)
    i += 1

proc run*(rules: var seq[SemanticRule]) : LR1Automata =
  var
    id = 1
    rulesDesugared = newTable[string, SemanticRuleDesugared]()
  for r in rules.mitems:
    r.expressionTree = buildTree(r.rhs)
    let
      tag = "tmpNode" & $id & "-"
      tmpName = tag & $r.expressionTree.id

    echo r.lhs.value ,"'s bracketSequence: ", bracketSequence(r.expressionTree)
    DP(r.expressionTree, tag, rulesDesugared)
    echo rulesDesugared
    if r.expressionTree.meet != rnRewrite:
      rulesDesugared[r.lhs.value] = rulesDesugared[tmpName]
      rulesDesugared[r.lhs.value].firstSetStatus = fsUncalculated
      rulesDesugared.del(tmpName)
    else:
      rulesDesugared[r.lhs.value] =
        SemanticRuleDesugared(
          firstSetStatus: fsUncalculated,
          rhs: @[@[Symbol(stype: sNonterminal, value: tmpName)]],
          nullable: rulesDesugared[tmpName].nullable)
    id += 1
  echo "--------------------------------------------------------"
  echo "rulesDesugared: ", rulesDesugared
  echo "--------------------------------------------------------"

  var a: LR1Automata
  constructLR1Automata(a, rulesDesugared)
  for k, s in a.states.pairs:
    echo fmt"{k}: {s.kernal} | {s.closure}"
  for id, s in a.states.pairs:
    for k, v in s.goto:
      echo fmt"F[{id}][{k}] = {v}"
    for k,v in s.actions:
      echo fmt"Action[{id}][{k}] = {v}"
  a
