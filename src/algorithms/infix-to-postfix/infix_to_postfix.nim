# Assume that every token costs one char

type
  node = ref object
    left, right: node
    value: char

func isVariable(x : char) : bool =
  ('a' <= x and x <= 'z') or ('A' <= x and x <= 'Z')

func isOperator(x : char) : bool =
  x == '+' or x == '-' or x == '*' or x == '/' or x == '^'

func precedence(x : char) : int =
  assert isOperator(x)
  case x:
    of '+', '-': return 1
    of '*', '/': return 2
    of '^': return 3
    else: return -1

func associtive(x : char) : int = # 1 for left to right, -1 for right to left
  assert isOperator(x)
  case x:
    of '+', '-': return 1
    of '*', '/': return 1
    of '^': return -1
    else: return -1

proc postorder(x : node) =
  if x != nil:
    postorder(x.left)
    postorder(x.right)
    stdout.write(x.value & " ")

var
  expression : string
  charStack : seq[char]
  nodeStack : seq[node]

discard readLine(stdin, expression)
expression = "(" & expression & ")" # Force the stack to be cleared
for i in expression:
  echo "read:", i
  if isVariable(i):
    nodeStack.add(node(left: nil, right: nil, value: i))
  elif i == '(':
    charStack.add('(')
  elif isOperator(i):
    while charStack.len() != 0 and
          charStack[^1] != '(' and
          (precedence(charStack[^1]) > precedence(i) or
           (precedence(i) == precedence(charStack[^1]) and associtive(i) == 1)):
      let
        op = charStack.pop()
        tr = nodeStack.pop()
        tl = nodeStack.pop()
      nodeStack.add(node(left: tl, right: tr, value: op))
    charStack.add(i)
  elif i == ')':
    while charStack[^1] != '(':
      let
        op = charStack.pop()
        tr = nodeStack.pop()
        tl = nodeStack.pop()
      nodeStack.add(node(left: tl, right: tr, value: op))
    discard charStack.pop()
  echo "charStack: ", charStack
  stdout.write("nodeStack: @[")
  for i in nodeStack:
    stdout.write(i.value, ", ")
  echo "]"
echo "fin"

postorder(nodeStack[^1])
stdout.writeLine("")
