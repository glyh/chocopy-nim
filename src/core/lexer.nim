import os, streams, logging, re, strformat, algorithm

var logger = newConsoleLogger()
type
  TokenType = enum
    ttInt
    ttString
    ttPreserved # Indent, Dedent, if, for, ",", ":", etc.
    ttId
    ttSymbol
    ttLeadingWhiteSpace
    ttWhiteSpace
    ttIndent
    ttDedent
  Token = object
    ttype: TokenType
    line: int
    value: string
  TokenMatch = object
    ttype: TokenType
    pattern: Regex

var patternList: seq[TokenMatch] = @[]
let symbol = ["(", ")", "[", "]", ":", "->", "=", "+", "-", "*", "//", "%",
                 "==", "!=", "<=", ">=", "<", ">", ","]

let preserved = ["pass", "def", "global",
                 "nonlocal", "if", "elif", "else", "while", "for", "in",
                 "return", "None", "True", "False", "not", "and", "or", "is"]

proc parse(path: string) =
  echo("Trying to read: ", path)
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
          echo line, p
          var success: bool = false
          for _, v in patternList:
            let matchedLength = matchLen(line, v.pattern, p)
            if matchedLength != -1:
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
              #echo "succ!!"
              break
          if not success:
            #echo line[p..^1].len, p, len(line)
            log(logger, lvlError,
              fmt("Can't recognize symbol at position {lineNumber}, {p}: \"{line[p..^1]}\""))
            break
        lineNumber += 1
      echo("Touching EOF!")
      echo("------------------------")
      for i in output:
        echo(i.ttype, ", ", i.value, ", ", i.line)
      echo("------------------------")

    except IOError as e:
      log(logger, lvlError, fmt("{e.name}, {e.msg}"))
      return
  else:
    log(logger, lvlError, "The input file doesn't exists")

proc init() =
  add(patternList, TokenMatch(ttype:ttInt, pattern: re("[+-]?[0-9]+")))
  add(patternList,
      TokenMatch(ttype:ttString, pattern: re("\"(\\.|[^\"\\\\])*\"")))
  add(patternList,
      TokenMatch(ttype:ttId, pattern: re("[a-zA-Z_][a-zA-Z_0-9]*")))
  var tmp = "("
  for i, v in preserved:
    if i == len(preserved) - 1:
      add(tmp, v & ")(?![a-zA-Z_0-9])")
    else:
      add(tmp, v & "|")
  add(patternList, TokenMatch(ttype:ttPreserved, pattern: re(tmp)))
  tmp = ""
  for i, v in symbol:
    if i == len(preserved) - 1:
      add(tmp, "\\" & v)
    else:
      add(tmp, "\\" & v & "|")
  add(patternList, TokenMatch(ttype:ttSymbol, pattern: re(tmp)))
  add(patternList, TokenMatch(ttype:ttLeadingWhiteSpace, pattern: re("^\\s+")))
  add(patternList, TokenMatch(ttype:ttWhiteSpace, pattern: re("[\\s\\r\\n]+")))


proc run*() =
  init()
  if paramCount() >= 2:
    for i in 2 .. paramCount():
      parse(paramStr(i))
