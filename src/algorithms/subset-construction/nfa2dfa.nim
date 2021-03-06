import strscans, sequtils, algorithm, tables #{ hashmap #}
type
  edge = tuple[to: int, next: int, val: int] # We have integer weights on edges

var
  line: string
  n, m, n_accepting, sigma: int
  E : seq[edge] = newSeq[edge](1)
  head : seq[int]
  marked : seq[bool]
  accept: seq[bool]

proc link(a: int, b: int , c : int) =
  var id {.global.} = 1
  E.add((b, head[a], c))
  head[a] = id
  id += 1

proc epsilon_closure(s : seq[int]) : seq[int] = # O(nm)
  # set is limited, so I don't use it
  var
    s_new = s
    p = 0
  for i in countup(1, n): marked[i] = false
  for i in s: marked[i] = true
  while p < s_new.len():
    var j: int = head[s_new[p]]
    while j != 0:
      if E[j].val == 0 and not marked[E[j].to]:
        s_new.add(E[j].to)
        marked[E[j].to] = true
      j = E[j].next
    p += 1
  #echo "epsilon_closure(", s, ") = ", sorted(s_new)
  sorted(s_new)

proc move(s : seq[int], v : int) : seq[int] = #O(nm)
  assert v != 0
  var s_new = newSeq[int]()
  for i in s:
    var j: int = head[i]
    while j != 0:
      if E[j].val == v:
        s_new.add(E[j].to)
      j = E[j].next
  #echo "move(", s, ", ", v, ") = ", sorted(s_new)
  sorted(s_new)

discard readLine(stdin, line)
discard scanf(line, "$i $i $i $i", n, m, n_accepting, sigma)
# sigma is the size of charset
head = newSeq[int](n + 1)
marked = newSeq[bool](n + 1)
accept = newSeq[bool](n + 1)
for i in countup(1, n_accepting):
  var a : int
  discard readLine(stdin, line)
  discard scanf(line, "$i", a)
  accept[a] = true
for i in countup(1, m):
  var a, b, c : int
  discard readLine(stdin, line)
  discard scanf(line, "$i $i $i", a, b, c)
  # we use weight of 0 to represent epsilon_edge
  link(a, b, c)

var
  dStates : seq[seq[int]] = @[epsilon_closure(@[1])]
  # we take 1 as the starting point
  i = 0
  f : Table[int, Table[int, int]] = initTable[int, Table[int, int]]()
while i < dStates.len(): # O(n * (2^n) ^ 2 * m * sigma)
  let cur = dStates[i]
  f[i] = initTable[int, int]()
  for j in countup(1, sigma): # 0 represents epsilon
    let U = epsilon_closure(move(cur, j))
    var
        flag = false
        p = 0
    for k in dStates:
      # There might be someway to improve the performance of judging whether
      # there's a duplicate set by hashing.
      if k == U:
        f[i][j] = p
        flag = true
        break
      p += 1
    if not flag:
      dStates.add(U)
      f[i][j] = dStates.len() - 1
  i += 1

i = 0
for j in dStates: # O(n*2^n)
  echo (i + 1), ":",  j, ", accepting: ",
    any(j, proc(x: int): bool = return accept[x])
  i += 1

for k, v in f.pairs():
  for k1, v1 in v.pairs():
    echo "f[", k + 1, ", ", k1, "] = ", v1 + 1
