import strformat, tables, algorithm
# "(a|)" and "(|a)" is illegal, since | should always be binary, please use "a?"
type
  TokenType = enum
    literal, operator, charset, lbracket, rbracket, wildcard, accept
  OperatorType = enum
    opConcat, opKleen, opPositive, opOptional, opOr
  Associative = enum
    LtoR, RtoL
  Token = ref object of RootObj
    ttype: TokenType
    pos: int
  TokenStream = object
    tokens: seq[Token]
    posCount: int
    posMap: seq[Token]
  Literal = ref object of Token
    value: char
  Operator = ref object of Token
    otype: OperatorType
  Charset = ref object of Token
    choice: set[char]
  Node = ref object
    left, right: Node
    nullable: bool
    firstpos, lastpos: seq[int]
    value: Token
  Regex = object
    posMap: seq[Token]
    expressionTree: Node
    followpos: seq[seq[int]]
    DStates: seq[seq[int]]
    DTrans: Table[int, Table[char, int]]
    DAccept: seq[bool]

func isOperator(c : char) : bool =
  c in {'|', '+', '*', '?'}

func toOperator(c : char) : OperatorType =
  case c:
    of '|': return opOr
    of '+': return opPositive
    of '*': return opKleen
    of '?': return opOptional
    else: assert false

func precedence(op: OperatorType) : int =
  case op:
    of opOr: 1
    of opConcat: 2
    of opPositive, opOptional, opKleen: 3

func unary(op: OperatorType) : bool =
  case op:
    of opOr, opConcat: false
    of opPositive, opOptional, opKleen: true

func associtive(op : OperatorType) : Associative =
  case op:
    of opOr, opConcat: LtoR
    of opPositive, opOptional, opKleen: LtoR

var
  nodeStack : seq[Node]
  tokenStack : seq[Token]

proc eliminate() =
  let
    token = tokenStack.pop()
    tr = nodeStack.pop()
  assert token.ttype == operator
  let
    token_casted = cast[Operator](token)
    op = token_casted.otype
  if unary(op):
    nodeStack.add(Node(left: tr, right: nil, value: token))
  else:
    let tl = nodeStack.pop()
    nodeStack.add(Node(left: tl, right: tr, value: token))

func formatToken(t: Token) : string =
  case t.ttype:
    of literal:
      let l = cast[Literal](t)
      return fmt"[Literal: '{l.value}' at {l.pos}]"
    of operator:
      let o = cast[Operator](t)
      return fmt"[Operator: '{o.otype}']"
    of charset:
      let c = cast[Charset](t)
      return fmt"[Charset: '{c.choice}' at {c.pos}]"
    of lbracket:
      return "[Lbracket: (]"
    of rbracket:
      return "[Rbracket: )]"
    of wildcard:
      return fmt"[Wildcard: * at {t.pos}]"
    of accept:
      return "[Accept]"

proc postorder(t: Node) =
  if t != nil:
    postorder(t.left)
    postorder(t.right)
    stdout.write(formatToken(t.value), " ")

proc unique[T](s: var seq[T]) =
  var tmp: seq[T] = @[]
  for i in s:
    if tmp.len() != 0 and i == tmp[^1]:
      continue
    tmp.add(i)
  s = tmp

proc dp(t: Node, r: var Regex) =
  assert t != nil
  if t.left != nil: dp(t.left, r)
  if t.right != nil: dp(t.right, r)
  case t.value.ttype:
    of literal, charset, wildcard, accept:
      t.firstpos = @[t.value.pos]
      t.lastpos = @[t.value.pos]
      t.nullable = false
    of operator:
      let op = cast[Operator](t.value)
      case op.otype:
        of opConcat:
          t.firstpos = t.left.firstpos
          if t.left.nullable: t.firstpos &= t.right.firstpos
          t.lastpos = t.right.lastpos
          if t.right.nullable: t.lastpos &= t.left.lastpos
          t.nullable = t.left.nullable and t.right.nullable
          for i in t.left.lastpos:
            r.followpos[i] &= t.right.firstpos
        of opKleen:
          t.firstpos = t.left.firstpos
          t.lastpos = t.left.lastpos
          t.nullable = true
          for i in t.lastpos:
            r.followpos[i] &= t.firstpos
        of opPositive:
          t.firstpos = t.left.firstpos
          t.lastpos = t.left.lastpos
          t.nullable = t.left.nullable
          for i in t.lastpos:
            r.followpos[i] &= t.firstpos
        of opOptional:
          t.firstpos = t.left.firstpos
          t.lastpos = t.left.lastpos
          t.nullable = true
        of opOr:
          t.firstpos = t.left.firstpos & t.right.firstpos
          t.lastpos = t.left.lastpos & t.right.lastpos
          t.nullable = t.left.nullable or t.right.nullable
      sort(t.firstpos)
      unique(t.firstpos)
      sort(t.lastpos)
      unique(t.lastpos)
      #echo formatToken(t.value), t.firstpos, t.lastpos
    else:
      assert false

proc parseToken(input: string) : TokenStream =
  let input = "(" & input & ")"
  nodeStack = @[]
  tokenStack = @[]
  type lastWitnessCharset = enum mnothing, mdash, mliteral
  var
    pos = 1
    posMap : seq[Token] = @[Token()]
    # Stores the index of patterns that really "matches" input string,
    # like "a", ".", "[0-9]"

    escaped = false
    tokens : seq[Token] = @[]
    needConcat: bool = false

    meet: lastWitnessCharset = mnothing # Dealing with charset
    lastChar: char = '\0'
    inCharset = false
    curCharset : set[char] = {}
  for i in input:
    if inCharset:
      if escaped:
        meet = mliteral
        lastChar = i
        curCharset.incl(i)
        escaped = false
      elif i == '-':
        case meet:
          of mnothing:
            curCharset.incl('-')
            meet = mliteral
            lastChar = i
          of mdash:
            assert i >= lastChar
            for j in lastChar .. i:
              curCharset.incl(j)
            meet = mnothing
          of mliteral:
            meet = mdash
      elif i == ']':
        case meet:
          of mnothing, mliteral: discard # great
          of mdash:
            curCharset.incl('-')
        if needConcat: tokens.add(Operator(ttype: operator, otype: opConcat))
        tokens.add(Charset(ttype: charset, choice: curCharset, pos: pos))
        posMap.add(Charset(ttype: charset, choice: curCharset, pos: pos))
        pos += 1
        needConcat = true
        inCharset = false
      else:
        case meet:
          of mnothing:
            curCharset.incl(i)
            meet = mliteral
            lastChar = i
          of mdash:
            assert i >= lastChar
            for j in lastChar .. i:
              curCharset.incl(j)
            meet = mnothing
          of mliteral:
            curCharset.incl(i)
            lastChar = i
    else:
      if escaped:
        if needConcat: tokens.add(Operator(ttype: operator, otype: opConcat))
        tokens.add(Literal(ttype: literal, value: i, pos: pos))
        posMap.add(Literal(ttype: literal, value: i, pos: pos))
        pos += 1
        needConcat = true
        escaped = false
      elif i == '\\':
        escaped = true
      elif isOperator(i):
        tokens.add(Operator(ttype: operator, otype: toOperator(i)))
        if toOperator(i) == opOr: needConcat = false
      elif i == '(':
        if needConcat: tokens.add(Operator(ttype: operator, otype: opConcat))
        tokens.add(Token(ttype: lbracket))
        needConcat = false
      elif i == ')':
        tokens.add(Token(ttype: rbracket))
        needConcat = true
      elif i == '[':
        meet = mnothing
        inCharset = true
        curCharset = {}
      elif i == '.':
        if needConcat: tokens.add(Operator(ttype: operator, otype: opConcat))
        tokens.add(Token(ttype: wildcard, pos: pos))
        posMap.add(Token(ttype: wildcard, pos: pos))
        pos += 1
        needConcat = true
      else:
        if needConcat: tokens.add(Operator(ttype: operator, otype: opConcat))
        tokens.add(Literal(ttype: literal, value: i, pos: pos))
        posMap.add(Literal(ttype: literal, value: i, pos: pos))
        pos += 1
        needConcat = true
  return TokenStream(tokens: tokens, posCount: pos - 1, posMap: posMap)

proc buildTree(t: TokenStream) : Regex =
  for i in t.tokens:
    case i.ttype:
      of literal, charset, wildcard:
        nodeStack.add(Node(left: nil, right: nil, value: i))
      of operator:
        let
          oi = cast[Operator](i)
          pi = precedence(oi.otype)
          ai = associtive(oi.otype)
        while tokenStack.len() != 0 and tokenStack[^1].ttype == operator:
          let
            olas = cast[Operator](tokenStack[^1])
            plas = precedence(olas.otype)
          if plas > pi or (plas == pi and ai == LtoR):
            eliminate()
          else: break
        tokenStack.add(i)
      of lbracket:
        tokenStack.add(i)
      of rbracket:
        while tokenStack[^1].ttype == operator:
          eliminate()
        discard tokenStack.pop() # pop lbracket
      else: assert false
  #[
    echo "built posMap: "
    for k, v in t.posMap & @[Token(ttype: accept, pos: t.posCount + 1)]:
      echo k, formatToken(v)
    echo "----------"
  ]#
  return Regex(expressionTree: Node(left: nodeStack.pop(),
               right: Node(left: nil,
                           right: nil,
                           value: Token(ttype: accept, pos: t.posCount + 1)),
               value: Operator(ttype: operator, otype: opConcat)),
               posMap: t.posMap & @[Token(ttype: accept, pos: t.posCount + 1)])

proc buildDFA(r: var Regex) =
  r.DTrans = initTable[int, Table[char, int]]()
  r.DStates = @[r.expressionTree.firstpos]
  var
    existStates = initTable[seq[int], int]()
    i = 0
    validInput : set[char] = {}
  existStates[r.expressionTree.firstpos] = 0
  while i < r.DStates.len():
    r.DTrans[i]= initTable[char, int]()
    var canAccept = false
    var wildFollowpos: seq[int] = @[]
    for id in r.DStates[i]:
      let tokenAtPos = r.posMap[id]
      case tokenAtPos.ttype:
        of literal:
          validInput.incl(cast[Literal](tokenAtPos).value)
        of wildcard:
          wildFollowpos &= r.followpos[id]
        of charset:
          for c in cast[Charset](tokenAtPos).choice:
            validInput.incl(c)
        of accept: canAccept = true
        else: assert false
    r.DAccept.add(canAccept)
    if wildFollowpos.len() != 0:
      sort(wildFollowpos)
      unique(wildFollowpos)
      if existStates.contains(wildFollowpos):
        r.DTrans[i]['\0'] = existStates[wildFollowpos]
      else:
        r.DTrans[i]['\0'] = r.DStates.len()
        existStates[wildFollowpos] = r.DStates.len()
        r.DStates.add(wildFollowpos)
    for c in validInput:
      var cFollowpos = wildFollowpos
      for id in r.DStates[i]:
        let tokenAtPos = r.posMap[id]
        case tokenAtPos.ttype:
          of wildcard, accept: discard
          of literal:
            if (cast[Literal](tokenAtPos)).value == c:
              cFollowpos &= r.followpos[id]
          of charset:
            if c in (cast[Charset](tokenAtPos)).choice:
              cFollowpos &= r.followpos[id]
          else: assert false
        if cFollowpos.len() != 0:
          sort(cFollowpos)
          unique(cFollowpos)
          if existStates.contains(cFollowpos):
            r.DTrans[i][c] = existStates[cFollowpos]
          else:
            r.DTrans[i][c] = r.DStates.len()
            existStates[cFollowpos] = r.DStates.len()
            r.DStates.add(cFollowpos)
    i += 1

proc parseRegex(input : string) : Regex =
  let t = parseToken(input)
  var r = buildTree(t)
  r.followpos = newSeq[seq[int]](t.posCount + 2)
  # [1..n+1], n+1 preserved for the success node
  dp(r.expressionTree, r)
  # echo "posMap: "
  # for id, v in r.posMap:
  #   if id != 0:
  #     echo fmt"{id} -> {formatToken(v)}, followpos = {r.followpos[id]}"
  buildDFA(r)
  echo "DStates(0 is the start state): "
  for id, v in r.DStates:
    echo fmt"{id}: {v}, accept={r.DAccept[id]}"
  echo "DTrans: "
  for k, v in r.DTrans.pairs():
    for k1, v1 in v.pairs():
      echo fmt"f[{k}][{k1}]={v1}"
  return r

var input: string
discard readLine(stdin, input)
var r = parseRegex(input)
postorder(r.expressionTree)
echo ""
