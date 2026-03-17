def repeated(n, f, x):
    if n == 0:
        return x
    return f(repeated(n-1, f, x))

def c(n):
    return lambda f: lambda x: repeated(n, f, x)

plus1 = lambda x: x + 1

def toint(c):
    return c(plus1)(0)

c0 = c(0)
c1 = c(1)
c5 = c(5)

cs = lambda n: lambda f: lambda x: f(n(f)(x))

cplus = lambda m: lambda n: lambda f: lambda x: m(f)(n(f)(x))
cpluss = lambda m: m(cs)

cmult = lambda m: lambda n: lambda f: m(n(f))
cmultt = lambda m: lambda n: m(cplus(n))(c0)

cexp = lambda m: lambda n: n(m)
cexpp = lambda m: lambda n: n(cmult(m))(c1)

cTrue = lambda x: lambda y: x
cFalse = lambda x: lambda y: y

def tobool(b):
    return b(True)(False)

