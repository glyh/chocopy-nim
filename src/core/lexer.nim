import algorithm, os, streams, logging, re, strformat, parseutils
import definition

var logger = newConsoleLogger()

proc scan(path: string) : seq[ChoToken] =
  if fileExists(path):
    var s = newFileStream(path, fmRead)
    defer: close(s)
    var
      output: seq[ChoToken] = @[]
      lineNumber = 1
      line: string
      indentStack: seq[int] = @[0]
    try:
      while readLine(s, line):
        var p: int = 0
        let lineLength = len(line)
        while p < lineLength:
          var success: bool = false
          for k, v in tokenPattern.items():
            let matchedLength = matchLen(line, v, p)
            if matchedLength != -1:
              if p == 0 and k != ctLeadingWhiteSpace:
                while indentStack[^1] != 0:
                  discard indentStack.pop()
                  output.add(ChoToken(ctype: ctDedent, line: lineNumber))
              let ct = k
              case ct:
                of ctLeadingWhiteSpace:
                  # deal with indent and dedent
                  if matchedLength > indentStack[^1]:
                    indentStack.add(matchedLength)
                    output.add(ChoToken(ctype: ctIndent, line: lineNumber))
                  elif matchedLength < indentStack[^1]:
                    let pos = binarySearch(indentStack, matchedLength)
                    if pos != -1:
                      while indentStack[^1] != matchedLength:
                        discard indentStack.pop()
                        output.add(ChoToken(ctype: ctDedent, line: lineNumber))
                    else:
                      log(logger, lvlError,
                        fmt("Unmatched dedent at position {lineNumber}, {p}"))
                of ctWhiteSpace:
                  discard
                of ctInt:
                  var i: int
                  discard parseInt(line[p ..< p + matchedLength], i)
                  output.add(ChoToken(ctype: ctInt, vint: i))
                of ctString, ctPreserved, ctId, ctSymbol:
                  output.add(ChoToken(ctype: ct,
                    vstr: line[p ..< p + matchedLength]))
                else: discard
              p += matchedLength
              success = true
              break
          if not success:
            logger.log(lvlError,
              fmt("Can't recognize symbol at position {lineNumber}, {p}: \"{line[p..^1]}\""))
            break
        output.add(ChoToken(ctype: ctNewLine, line: lineNumber))
        lineNumber += 1
      return output
    except IOError as e:
      logger.log(lvlError, fmt("{e.name}, {e.msg}"))
      return @[]
  else:
    logger.log(lvlError, "The input file doesn't exists")
    return @[]

proc run*() =
  if paramCount() >= 2:
    for i in 2 .. paramCount():
      echo scan(paramStr(i))
