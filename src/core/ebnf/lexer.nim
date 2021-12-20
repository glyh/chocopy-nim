import
  os, streams, logging, re, strformat, json, sequtils, tables, sets,
  strutils,
  definition
var logger = newConsoleLogger()

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
          for t, pattern in tokenPattern.items():
            let matchedLength = matchLen(line, pattern, p)
            let ty = t # for runtime discriminator
            assert ty != ttAccept
            if matchedLength != -1:
              case ty:
                of ttWhiteSpace: discard
                of ttCommentHead: meetComment = true
                of ttTerminal, ttNonterminal, ttWords:
                  add(output, Token(ttype: ty, line: lineNumber,
                      value: line[p ..< p + matchedLength]))
                of ttNil:
                  add(output, Token(ttype: ty, line: lineNumber))
                of ttOperator:
                  add(output, Token(ttype: ttOperator,
                                    line: lineNumber,
                                    otype: operatorMap[line[p]]))
                else:
                  add(output, Token(ttype: ty, line: lineNumber))
              p += matchedLength
              success = true
              break
          if not success:
            log(logger, lvlError,
                fmt("Can't recognize symbol at position " &
                    "{lineNumber}, {p}: \"{line[p..^1]}\""))
            break
          if meetComment: break
        add(output, Token(ttype: ttNewLine, line: lineNumber))
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
          tokens.delete(i..i)
        meetProduction = false
      of ttProduce:
        meetProduction = true
      else:
        discard

  # Distinguish terminals and nonterminals, unescape terminals
  var names : HashSet[string]
  meetProduction = false

  for i in tokens:
    case i.ttype:
      of ttNewline:
        meetProduction = false
      of ttProduce:
        meetProduction = true
      of ttWords:
        if not meetProduction:
          names.incl(i.value)
      else:
        discard

  for i in tokens.mitems:
    case i.ttype:
      of ttWords:
        var t: Token =
          if names.contains(i.value):
            Token(ttype: ttNonterminal, line: i.line, value: i.value)
          else:
            Token(ttype: ttTerminal, line: i.line, value: i.value)
        t.pos = i.pos
        i = t
      of ttTerminal:
        if i.value[0] == '"':
          i.value = unescape(i.value)
      else: discard
  return tokens

proc run*(path: string) : seq[Token] =
  var tokens = read(path)
  if len(tokens) == 0: return @[]
  tokens = preprocess(tokens)
  if len(tokens) == 0: return @[]
  return tokens
