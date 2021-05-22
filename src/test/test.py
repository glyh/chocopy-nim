a = 24
b = 18
while True:
    if b == 0:
        break
    else:
        a, b = b, a % b
print(a)
