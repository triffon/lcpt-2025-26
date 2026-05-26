def fact(n):
    if n == 0:
        return 1
    return n * fact(n-1)

def factcps(k,n):
    if n == 0:
        return k(1)
    return factcps(lambda res: k(n*res), n-1)
