import re, strutils, strformat
type
  ChoTokenType* = enum
    ctInt
    ctString
    ctPreserved # if, for, etc.
    ctId
    ctSymbol # ",", ":", etc.
    ctLeadingWhiteSpace
    ctWhiteSpace
    ctIndent
    ctDedent
    ctNewLine
  ChoToken* = object
    line*: int
    case ctype*: ChoTokenType:
      of ctInt:
        vint*: int
      of ctString, ctPreserved, ctId, ctSymbol:
        vstr*: string
      of ctIndent, ctDedent, ctNewLine, ctWhiteSpace, ctLeadingWhiteSpace:
        discard

const
  symbols* = ["\\(", "\\)", "\\[", "\\]", ":", "->", "\\+", "-", "\\*", "//",
              "%", "==", "=", "!=", "<=", ">=", "<", ">", ","]
  preserveds* = ["pass", "def", "global",
                 "nonlocal", "if", "elif", "else", "while", "for", "in",
                 "return", "None", "True", "False", "not", "and", "or", "is"]
let
  tokenPattern* = {
    ctInt: re("[+-]?[0-9]+"),
    ctString: re("\"(\\.|[^\"\\\\])*\""),
    ctId: re("[a-zA-Z_][a-zA-Z_0-9]*"),
    ctPreserved: re("(" & preserveds.join("|") & ")(?![a-zA-Z_0-9])"),
    ctSymbol: re(symbols.join("|")),
    ctLeadingWhiteSpace: re("^\\s+"),
    ctWhiteSpace: re("[\\s\\r\\n]+")
  }

func `$`*(t: ChoToken): string =
  case t.ctype:
    of ctInt:
      fmt"[{t.ctype}, vint: {t.vint}]"
    of ctString, ctPreserved, ctId, ctSymbol, ctLeadingWhiteSpace:
      fmt"[{t.ctype}, vstr: {t.vstr}]"
    of ctIndent, ctDedent, ctNewLine, ctWhiteSpace:
      fmt"[{t.ctype}]"
