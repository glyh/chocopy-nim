import algorithm, os, streams, logging, re, strformat, json

var logger = newConsoleLogger()
type
  TokenType = enum
    ttInt
    ttString
    ttPreserved # if, for, etc.
    ttId
    ttSymbol # ",", ":", etc.
    ttLeadingWhiteSpace
    ttWhiteSpace
    ttIndent
    ttDedent
    ttNewLine
  Token = object
    ttype: TokenType
    line: int
    value: string
  TokenMatch = object
    ttype: TokenType
    pattern: Regex

var patternList: seq[TokenMatch] = @[]
let symbol = ["\\(", "\\)", "\\[", "\\]", ":", "->", "\\+", "-", "\\*", "//",
              "%", "==", "=", "!=", "<=", ">=", "<", ">", ","]
# Escape twice because of the regex.

let preserved = ["pass", "def", "global",
                 "nonlocal", "if", "elif", "else", "while", "for", "in",
                 "return", "None", "True", "False", "not", "and", "or", "is"]

func toJson(tokens: seq[Token]): string =
  $(%* tokens)

proc scan(path: string) =
  #echo("Trying to read: ", path)
  if fileExists(path):
    var s = newFileStream(path, fmRead)
    defer: close(s)
    var output: seq[Token] = @[]
    var lineNumber = 1
    var line: string
    var indentStack: seq[int] = @[0]
    try:
      while readLine(s, line):
        var p: int = 0
        let lineLength = len(line)
        while p < lineLength:
          var success: bool = false
          for _, v in patternList:
            let matchedLength = matchLen(line, v.pattern, p)
            if matchedLength != -1:
              if p == 0 and v.ttype != ttLeadingWhiteSpace:
                while indentStack[^1] != 0:
                  discard pop(indentStack)
                  add(output, Token(ttype: ttDedent, line: lineNumber,
                    value: ""))
              case v.ttype:
                of ttLeadingWhiteSpace:
                  # deal with indent and dedent
                  if matchedLength > indentStack[^1]:
                    add(indentStack, matchedLength)
                    add(output, Token(ttype: ttIndent, line: lineNumber,
                        value: line[p ..< p + matchedLength]))
                  elif matchedLength < indentStack[^1]:
                    let pos = binarySearch(indentStack, matchedLength)
                    if pos != -1:
                      while indentStack[^1] != matchedLength:
                        discard pop(indentStack)
                        add(output, Token(ttype: ttDedent, line: lineNumber,
                          value: line[p ..< p + matchedLength]))
                    else:
                      log(logger, lvlError,
                        fmt("Unmatched dedent at position {lineNumber}, {p}"))
                of ttWhiteSpace:
                  discard
                else:
                  add(output, Token(ttype: v.ttype, line: lineNumber,
                      value: line[p ..< p + matchedLength]))
              p += matchedLength
              success = true
              break
          if not success:
            log(logger, lvlError,
              fmt("Can't recognize symbol at position {lineNumber}, {p}: \"{line[p..^1]}\""))
            break
        add(output, Token(ttype: ttNewLine, line: lineNumber,
                    value: ""))
        lineNumber += 1

      var outStream = newFileStream(path & ".lex", fmWrite)
      if not isNil(outStream):
        defer: close(outStream)
        writeLine(outStream, toJson(output))
    except IOError as e:
      log(logger, lvlError, fmt("{e.name}, {e.msg}"))
      return
  else:
    log(logger, lvlError, "The input file doesn't exists")

proc init() =
  var
    preservedRegex = "("
    symbolRegex = ""

  for i, v in preserved:
    if i == len(preserved) - 1:
      add(preservedRegex, v & ")(?![a-zA-Z_0-9])")
    else:
      add(preservedRegex, v & "|")

  for i, v in symbol:
    if i == len(symbol) - 1:
      add(symbolRegex, v)
    else:
      add(symbolRegex, v & "|")

  patternList = @[
    TokenMatch(ttype:ttInt, pattern: re("[+-]?[0-9]+")),
    TokenMatch(ttype:ttString, pattern: re("\"(\\.|[^\"\\\\])*\"")),
    TokenMatch(ttype:ttId, pattern: re("[a-zA-Z_][a-zA-Z_0-9]*")),
    TokenMatch(ttype:ttPreserved, pattern: re(preservedRegex)),
    TokenMatch(ttype:ttSymbol, pattern: re(symbolRegex)),
    TokenMatch(ttype:ttLeadingWhiteSpace, pattern: re("^\\s+")),
    TokenMatch(ttype:ttWhiteSpace, pattern: re("[\\s\\r\\n]+"))
  ]


proc run*() =
  init()
  if paramCount() >= 2:
    for i in 2 .. paramCount():
      scan(paramStr(i))
