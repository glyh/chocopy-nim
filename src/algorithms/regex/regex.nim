type
  TokenType = enum
    literal, operator, charset, lbracket, rbracket, wildcard
  OperatorType = enum
    opConcat, opKleen, opPositive, opOptional, opOr
  Associative = enum
    LtoR, RtoL
  Token = ref object of RootObj
    ttype: TokenType
  Literal = ref object of Token
    value: char
  Operator = ref object of Token
    otype: OperatorType
  Charset = ref object of Token
    choice: set[char]
  Node = ref object
    left, right: Node
    value: Token
  Regex = object
    expressionTree: Node

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
    of opOr: return 1
    of opConcat: return 2
    of opPositive, opOptional, opKleen: return 3

func unary(op: OperatorType) : bool =
  case op:
    of opOr, opConcat: return false
    of opPositive, opOptional, opKleen: return true

func associtive(op : OperatorType) : Associative =
  case op:
    of opOr, opConcat: return LtoR
    of opPositive, opOptional, opKleen: return RtoL

var
  nodeStack :seq[Node]
  tokenStack :seq[Token]

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

proc postorder(t: Node) =
  if t != nil:
    postorder(t.left)
    postorder(t.right)
    case t.value.ttype:
      of literal:
        stdout.write("[Literal: '", cast[Literal](t.value).value, "'] ")
      of operator:
        stdout.write("[Operator: ", cast[Operator](t.value).otype, "] ")
      of charset:
        stdout.write("[Charset: ", cast[Charset](t.value).choice, "] ")
      of lbracket:
        stdout.write("[Lbracket: (] ")
      of rbracket:
        stdout.write("[Rbracket: )] ")
      of wildcard:
        stdout.write("[Wildcard: *] ")

proc parseRegex(input : string) : Regex =
  let input = "(" & input & ")"
  nodeStack = @[]
  tokenStack = @[]
  type lastWitnessCharset = enum mnothing, mdash, mliteral
  var
    escaped = false
    tokens : seq[Token] = @[]
    needConcat: bool = false

    meet: lastWitnessCharset = mnothing
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
        tokens.add(Charset(ttype: charset, choice: curCharset))
        needConcat = true
        inCharset = false
      else:
        case meet:
          of mnothing:
            curCharset.incl(i)
            meet = mliteral
            lastChar = i
          of mdash:
            for j in lastChar .. i:
              curCharset.incl(j)
            meet = mnothing
          of mliteral:
            curCharset.incl(i)
            lastChar = i
        discard
    else:
      if escaped:
        if needConcat: tokens.add(Operator(ttype: operator, otype: opConcat))
        tokens.add(Literal(ttype: literal, value: i))
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
        lastChar = '\0'
        inCharset = true
        curCharset = {}
      elif i == '.':
        if needConcat: tokens.add(Operator(ttype: operator, otype: opConcat))
        tokens.add(Token(ttype: wildcard))
        needConcat = true
      else:
        if needConcat: tokens.add(Operator(ttype: operator, otype: opConcat))
        tokens.add(Literal(ttype: literal, value: i))
        needConcat = true
  #literal, operator, charset, lbracket, rbracket
  #for i in tokens:
  #  echo i.ttype

  for i in tokens:
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
        discard tokenStack.pop()
  return Regex(expressionTree: nodeStack.pop())


var input: string
discard readLine(stdin, input)
var r = parseRegex(input)
postorder(r.expressionTree)
echo ""
