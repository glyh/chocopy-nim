import strscans
type
  edge = ref object
    to: int
    next: edge

var
  head: seq[edge]
  n, m: int
  dfn, tlow, bel, stk: seq[int]
  s: string

discard stdin.readLine(s)
discard scanf(s, "$i $i", n, m)
head = newSeq[edge](n+1)
for i in 1..m:
  var a, b: int
  discard stdin.readLine(s)
  discard scanf(s, "$i $i", a, b)
  let e = edge(to: b, next: head[a])
  head[a] = e

dfn = newSeq[int](n+1)
tlow = newSeq[int](n+1)
bel = newSeq[int](n+1)

proc tarjan(x: int) =
  var id {.global.} = 1
  dfn[x] = id
  tlow[x] = id
  stk.add(x)
  id += 1
  var e = head[x]
  while e != nil:
    if dfn[e.to] == 0:
      tarjan(e.to)
      tlow[x] = min(tlow[x], tlow[e.to])
    elif bel[e.to] == 0:
      tlow[x] = min(tlow[x], dfn[e.to])
    e = e.next
  if dfn[x] == tlow[x]:
    while stk[^1] != x:
      bel[stk.pop()] = x
    bel[stk.pop()] = x

for i in 1..n:
  if dfn[i] == 0:
    tarjan(i)
for i in 1..n:
  echo i, ": ", bel[i]
