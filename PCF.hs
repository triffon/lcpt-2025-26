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

---------------------------

iseven = y (\self n -> cases (z n) tt
             (cases (z (p n)) ff
              (self (p (p n)))))

double = y (\self n -> cases (z n) 0
              (s (s (self (p n)))))

add = \m -> y (\self n -> cases (z n) m
                (s (self (p n))))

add2 = y (\self m n -> cases (z n) m
                       (s (self m (p n))))

add3 = y (\self m n -> cases (z m) n
                       (s (self (p m) n)))

-- eq = \m -> y (\self n -> cases (z n) (z m) ...
eq = y (\self m n -> cases (z n) (z m)
         (cases (z m) ff
                     (self (p m) (p n))))
