import os, streams, logging, re, strformat, json, sequtils, strutils
type
  TokenType = enum
    ttWhiteSpace
    ttCommentHead
    ttWords # Sometimes, it's not possible to distinguish terminals and nonterminals while scanning
    ttTerminal
    ttNonterminal
    ttProduce # ->
    ttLBracket # (
    ttRBracket # )
    ttOr # |
    ttNewline
    ttOptional #?
    ttKleen #*
    ttPositive #+
    ttNil # nil
  Token = object
    ttype : TokenType
    line : int
    value: string
  TokenMatch = object
    ttype: TokenType
    pattern: Regex
  SemanticRule = object
    lhs: Token
    rhs: seq[Token]
    closure: seq[tuple[rule: SemanticRule, pos: int]]
    goto: seq[tuple[rule: SemanticRule, pos: int]]
  NonterminalProperty = object
    first: seq[Token]
  LR1Item = object

var logger = newConsoleLogger()

var patternList: seq[TokenMatch] = @[]
#[
func toJson(tokens: seq[Token]): string =
  $(%* tokens)
]#

proc read(path: string) : seq[Token] =
  if fileExists(path):
    var s = newFileStream(path, fmRead)
    defer: close(s)
    var output: seq[Token] = @[]
    var lineNumber = 1
    var line: string
    try:
      while readLine(s, line):
        var p: int = 0
        let lineLength = len(line)
        var meetComment: bool = false
        while p < lineLength:
          var success: bool = false
          for _, v in patternList:
            let matchedLength = matchLen(line, v.pattern, p)
            if matchedLength != -1:
              case v.ttype:
                of ttWhiteSpace:
                  discard
                else:
                  add(output, Token(ttype: v.ttype, line: lineNumber,
                      value: line[p ..< p + matchedLength]))
              p += matchedLength
              success = true
              if v.ttype == ttCommentHead: meetComment = true
              break
          if not success:
            log(logger, lvlError,
              fmt("Can't recognize symbol at position {lineNumber}, {p}: \"{line[p..^1]}\""))
            break
          if meetComment: break
        add(output, Token(ttype: ttNewLine, line: lineNumber, value: ""))
        lineNumber += 1

      return output
    except IOError as e:
      log(logger, lvlError, fmt("{e.name}, {e.msg}"))
      return @[]
  else:
    log(logger, lvlError, "The input file doesn't exists")

proc preprocess(tokens: seq[Token]) : seq[Token] =
  var tokens = tokens

  # Arrange inputs so that each production rules is in a line.
  var meetProduction: bool = false
  for i in countdown(len(tokens) - 1, 0):
    case tokens[i].ttype:
      of ttNewline:
        if not meetProduction:
          tokens.delete(i, i)
        meetProduction = false
      of ttProduce:
        meetProduction = true
      else:
        discard

  # Distinguish terminals and nonterminals, unescape terminals
  var
    names :seq[string] = @[]
    meetNewline = false
  for i in tokens:
    case i.ttype:
      of ttNewline:
        meetNewline = true
      of ttWords:
        if meetNewline:
          meetNewline = false
          add(names, i.value)
      else:
        discard
  for i in countup(0, len(tokens) - 1):
    case tokens[i].ttype:
      of ttWords:
        if names.any(proc (x: string): bool = return x == tokens[i].value):
          tokens[i].ttype = ttNonterminal
        else:
          tokens[i].ttype = ttTerminal
      of ttTerminal:
        if tokens[i].value[0] == '"':
          tokens[i].value = unescape(tokens[i].value)
      else:
        discard
  return tokens

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

proc parse(path: string) =
  var tokens = read(path)
  if len(tokens) == 0: return
  tokens = preprocess(tokens)
  if len(tokens) == 0: return
  var rules = generate(tokens)
  #[
    var outStream = newFileStream(path & ".ebnf", fmWrite)
    if not isNil(outStream):
      defer: close(outStream)
      writeLine(outStream, toJson(output))
  ]#

proc init() =
  patternList = @[
    TokenMatch(ttype: ttWhiteSpace, pattern: re(" +")),
    TokenMatch(ttype: ttNil, pattern: re("(?![a-zA-Z_])nil(?![a-zA-Z_])")),
    TokenMatch(ttype: ttWords, pattern: re("[A-Za-z_]+")),
    TokenMatch(ttype: ttTerminal, pattern: re("\"(\\.|[^\"\\\\])*\"")),
    TokenMatch(ttype: ttCommentHead, pattern: re("#")),
    TokenMatch(ttype: ttProduce, pattern: re("->")),
    TokenMatch(ttype: ttLBracket, pattern: re("\\(")),
    TokenMatch(ttype: ttRBracket, pattern: re("\\)")),
    TokenMatch(ttype: ttOr, pattern: re("\\|")),
    TokenMatch(ttype: ttNewline, pattern: re("\n")),
    TokenMatch(ttype: ttOptional, pattern: re("\\?")),
    TokenMatch(ttype: ttKleen, pattern: re("\\*")),
    TokenMatch(ttype: ttPositive, pattern: re("\\+")),
    TokenMatch(ttype: ttTerminal, pattern: re("[^ ]+"))
    # Match any symbols like +, -, *, /
  ]

proc run*() =
  init()
  if paramCount() >= 2:
    for i in 2 .. paramCount():
      parse(paramStr(i))
