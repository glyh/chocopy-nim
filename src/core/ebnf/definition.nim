import re, tables, json, sets, strformat
type
  TokenType* = enum
    ttWhiteSpace, ttCommentHead, ttWords,
    #[ Sometimes, it's not possible to distinguish terminals and nonterminals
       while scanning ]#
    ttTerminal, ttNonterminal, ttProduce #[ -> ]#, ttLBracket, #[ ( ]#
    ttRBracket #[ ) ]#, ttNewline, ttNil #[ nil ]#, ttAccept, ttOperator
    #ttOr #[ | ]#, ttOptional #[ ? ]# ttKleen #[ * ]#, ttPositive #[ + ]#
  OperatorType* = enum
    opOr, opOptional, opKleen, opPositive, opConcat
    # |, ?, *, + (concat correspond to nothing)
  Token* = object
    line*: int
    case ttype*: TokenType:
      of ttTerminal, ttNonterminal, ttWords:
        value*: string
        pos*: int
      of ttOperator:
        otype*: OperatorType
      else: discard
  SemanticRule* = object
    lhs*: Token
    rhs*: seq[Token]
    expressionTree*: Node
    posCount*: int
    followPos*: seq[HashSet[int]]
    #closure*: seq[tuple[rule: SemanticRule, pos: int]]
    #goto*: seq[tuple[rule: SemanticRule, pos: int]]
  #[
    NonterminalProperty* = object
      nextPos*: seq[Token]
      firstPos*: seq[Token]
      lastPos*: seq[Token]
  ]#
  LR1Item* = object
  Node* = ref object
    left*, right*: Node
    nullable*: bool
    firstPos*, lastPos*: HashSet[int]
    value*: Token

const
  opPrecedence* :Table[OperatorType, int] = { opOr: 1,
                    opConcat: 2,
                    opOptional: 3, opKleen: 3, opPositive: 3 }.toTable()
  opUnary* = { opOr: false, opConcat: false,
               opOptional: true, opKleen: true,  opPositive: true }.toTable()
  operatorMap* = { '|' : opOr, '?' : opOptional,
                   '*' : opKleen, '+' : opPositive}.toTable()
#assert operatorMap['|'] == opOr
let
  tokenPattern* = {
    ttWhiteSpace: re("( |\t)+"),
    ttCommentHead: re("#"),
    ttNil: re("(?![a-zA-Z_])nil(?![a-zA-Z_])"),
    ttWords: re("[A-Za-z_]+"),
    ttProduce : re("->"),
    ttLBracket: re("\\("),
    ttRBracket: re("\\)"),
    ttNewline: re("\n"),
    ttOperator: re("\\||\\?|\\*|\\+"),
    ttTerminal: re("\"(\\.|[^\"\\\\])*\"|[^ ]+")
    # terminal quoted by "", or anything can't be matched by other patterns
  }
#[
    ttWhiteSpace, ttCommentHead, ttWords,
    ttTerminal, ttNonterminal, ttProduce , ttLBracket,
    ttRBracket , ttNewline, ttNil , ttAccept
]#

func toJson*(tokens: seq[Token]): string =
  $(%* tokens)

func formatToken*(t: Token): string =
  case t.ttype:
    of ttTerminal, ttNonterminal, ttWords:
      return fmt"[{t.ttype}, line: {t.line}, value: {t.value}, pos: {t.pos}]"
    of ttOperator:
      return fmt"[{t.ttype}, line: {t.line}, operator: {t.otype}]"
    else:
      return fmt"[{t.ttype}, line: {t.line}]"

proc postOrder*(t: Node) =
  if t != nil:
    postOrder(t.left)
    postOrder(t.right)
    stdout.write(formatToken(t.value), " ")
