def func():
    i = 1
    while True:
        yield i
        i += 1

y = func()
print [y.next() for _ in xrange(8)]
#prints 1,2,3,4,5,6,7,8