import re, tables, sets, strformat, hashes
type
  TokenType* = enum
    # These are eliminated after scanning
    ttWhiteSpace
    ttCommentHead
    ttWords #[ Sometimes, it's not possible to distinguish
               terminals and nonterminals while scanning ]#
    ttNewline
    ttProduce #[ -> ]#

    # These really mathes the input codes
    ttTerminal
    ttNonterminal
    ttNil

    # These are provided to improve the expressiveness of EBNF
    ttLBracket #[ ( ]#
    ttRBracket #[ ) ]#
    ttOperator

    # These are for parsing
    #ttStart
    ttAccept # or, endmark
  SymbolType* = enum
    sTerminal
    sNonterminal
    sAccept # endmark
    sNil
  OperatorType* = enum
    opOr, opOptional, opKleen, opPositive, opConcat
  firstSetStatusType* = enum
    fsUncalculated, fsCalculated, fsCalculating
    # |, ?, *, + (concat correspond to nothing)
  LR1ActionType* = enum
    lr1Shift, lr1Reduce, lr1Accept, lr1Error
  Token* = object
    line*: int
    case ttype*: TokenType:
      of ttAccept, #[ttStart,]# ttNil:
        pos1: int
      of ttTerminal, ttNonterminal, ttWords:
        pos2: int
        value*: string
      of ttOperator:
        otype*: OperatorType
      else: discard
  Symbol* = object
    case stype*: SymbolType:
      of sTerminal, sNonterminal:
        value*: string
      of sAccept, sNil: discard

  SemanticRule* = ref object
    lhs*: Token
    rhs*: seq[Token]
    expressionTree*: Node
    #posCount*: int # index: 1..posCount
    #followPos*: seq[HashSet[int]]
    #posMap*: seq[int]
    #firstSet*: HashSet[Symbol]
    #
    #id*: int
  SemanticRuleDesugared* = ref object
    rhs*: seq[seq[Symbol]]
    firstSet*: HashSet[Symbol]
    firstSetStatus*: firstSetStatusType
    nullable*: bool

  RuleNestLevel* = enum
    rnNone = 0
    rnMeetConcat = 1
    rnMeetOr = 2
    rnRewrite = 3

  Node* = ref object
    left*, right*: Node
    value*: Token
    meet*: RuleNestLevel
    id*: int

  LR1Item* = tuple[rule: string, dot: tuple[p: int, q: int], lookahead: Symbol]
  LR1Action* = object
    case lraType*: LR1ActionType:
      of lr1Shift, lr1Accept:
        discard
      of lr1Reduce:
        tokenCount*: int
        output*: Symbol
      of lr1Error:
        message*: string
  LR1State* = ref object
    kernal*: HashSet[LR1Item]
    closure*: HashSet[LR1Item]
    goto*: TableRef[Symbol, int]
    actions*: TableRef[Symbol, LR1Action]
    # These to help you reduce (where to end the reduce)
    isHead*: HashSet[int] # stores ruleId
    isBody*: HashSet[int] # stores ruleId
  LR1Automata* = object
    states*: seq[LR1State]

const
  opPrecedence* :Table[OperatorType, int] = { opOr: 1,
                    opConcat: 2,
                    opOptional: 3, opKleen: 3, opPositive: 3 }.toTable()
  opUnary* = { opOr: false, opConcat: false,
               opOptional: true, opKleen: true,  opPositive: true }.toTable()
  operatorMap* = { '|' : opOr, '?' : opOptional,
                   '*' : opKleen, '+' : opPositive}.toTable()

let
  tokenPattern* = {
    ttWhiteSpace: re("( |\t)+"),
    ttCommentHead: re("#"),
    ttNil: re("(?<![A-Za-z_])nil(?![A-Za-z_])"),
    ttWords: re("[A-Za-z_]+"),
    ttProduce : re("->"),
    ttLBracket: re("\\("),
    ttRBracket: re("\\)"),
    ttNewline: re("\n"),
    ttOperator: re("\\||\\?|\\*|\\+"),
    ttTerminal: re("\"(\\.|[^\"\\\\])*\"|[^ ]+")
    # terminal quoted by "", or anything can't be matched by other patterns
  }

template pos*(t: Token) : int =
  case t.ttype:
      of ttAccept, ttNil#[, ttStart]#: t.pos1
      of ttTerminal, ttNonterminal, ttWords: t.pos2
      else:
        raise newException(
          ValueError,
          "Attempted to access a non existant field 'pos' for type Token")

template `pos=`*(t: Token, val: int) =
  case t.ttype:
      of ttAccept, ttNil#[, ttStart]#: t.pos1 = val
      of ttTerminal, ttNonterminal, ttWords: t.pos2 = val
      else:
        raise newException(
          ValueError,
          fmt"Attempted to set a non existant" &
          " field 'pos' for type Token(ttype: {t.ttype})")

#func max*(lhs: RuleNestLevel, rhs: RuleNestLevel): RuleNestLevel =
#  if lhs < rhs: rhs else: lhs

func `==`*(lhs: Symbol, rhs: Symbol): bool =
  lhs.stype == rhs.stype and
  (case lhs.stype:
    of sTerminal, sNonterminal: lhs.value == rhs.value
    #of sNonterminal: lhs.id == rhs.id
    else: true)

func `==`*(lhs: LR1Action, rhs: LR1Action): bool =
  lhs.lraType == rhs.lraType and
  (case lhs.lraType:
    of lr1Shift, lr1Accept: true
    of lr1Reduce: lhs.tokenCount == rhs.tokenCount and lhs.output == rhs.output
    of lr1Error: lhs.message == rhs.message)

func `$`*(a: LR1Action): string =
  case a.lraType:
    of lr1Shift, lr1Accept: fmt"[{a.lraType}]"
    of lr1Reduce:
      fmt"[{a.lraType}, tokenCount: {a.tokenCount}, output: {a.output}]"
    of lr1Error: fmt"[{a.lraType}, errorMessage: {a.message}]"

func `$`*(r: SemanticRuleDesugared): string =
  $(rhs: r.rhs)
func `$`*(r: SemanticRule): string =
  $(lhs: r.lhs, rhs: r.rhs)

func hash*(t: Symbol): Hash =
  var h: Hash = hash(ord(t.stype))
  case t.stype:
    of sTerminal, sNonterminal:
      h = h !& hash(t.value)
    #[
      of sNonterminal:
        h = h !& hash(t.id)
    ]#
    of sAccept, sNil: discard
  !$h

func `$`*(t: Token): string =
  case t.ttype:
    of ttTerminal, ttNonterminal, ttWords:
      fmt"[{t.ttype}, line: {t.line}, value: {t.value}, pos: {t.pos}]"
    of ttAccept, ttNil#[, ttStart]#:
      fmt"[{t.ttype}, line: {t.line}, pos: {t.pos}]"
    of ttOperator:
      fmt"[{t.ttype}, line: {t.line}, operator: {t.otype}]"
    else:
      fmt"[{t.ttype}, line: {t.line}]"
#func `$`*(s: LR1State): string =
  #let k = if s.kernal == nil: nil else: s.kernal
  #let c = if s.closure == nil: nil else: s.closure
  #let g = if s.goto == nil: nil else: s.goto
  #fmt"[kernal: {s}, closure: {c}, goto: {g}]"

func postOrder*(t: Node): string =
  if t != nil:
    postOrder(t.left) & postOrder(t.right) & $(t.value) & " "
  else: ""

func bracketSequence*(t: Node): string =
  if t == nil: ""
  else: fmt"({bracketSequence(t.left)} {t.value} {bracketSequence(t.right)})"
