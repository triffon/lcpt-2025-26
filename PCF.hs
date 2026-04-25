type N = Integer
type B = Bool

split (s, t) f = f s t
tt = True
ff = False
o = 0
s = (+1)
p 0 = 0
p n = n - 1
z = (==0)
cases True s t = s
cases False s t = t
y t = t (y t)
