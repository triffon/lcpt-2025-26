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

cnot = lambda b: lambda x: lambda y: b(y)(x)
cnott = lambda b: b(cFalse)(cTrue)

cand = lambda p: lambda q: p(q)(cFalse)
cor = lambda p: lambda q: p(cTrue)(q)

ciszero = lambda n: n(lambda b: cFalse)(cTrue)
ceven = lambda n: n(cnot)(cTrue)

cpair = lambda x: lambda y: lambda z: z(x)(y)
cleft = lambda p: p(cTrue)
cright = lambda p: p(cFalse)

def tointpair(p):
    return (toint(cleft(p)), toint(cright(p)))

cpstep = lambda p: cpair(cs(cleft(p)))(cleft(p))

cp = lambda n: cright(n(cpstep)(cpair(c0)(c0)))

cfactstep = lambda p: \
              cpair(cs(cleft(p))) \
                   (cmult(cs(cleft(p)))(cright(p)))

cfact = lambda n: cright(n(cfactstep)(cpair(c0)(c1)))

Y = lambda F: (lambda x: F(x(x)))(lambda x: F(x(x)))

cgammafact = lambda f: lambda n: \
               ciszero(n)(c1) \
                         (cmult(n)(f(cp(n))))


cgammafactt = lambda f: lambda n: \
                ciszero(n)(lambda z: c1(z)) \
                          (lambda z: cmult(n)(f(cp(n)))(z))

# cfactt = Y(cgammafact)

bad = lambda x: x / 0

Z = lambda F: (lambda x: F(lambda z: x(x)(z))) \
              (lambda x: F(lambda z: x(x)(z)))

cfactt = Z(cgammafactt)
