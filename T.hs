type N = Integer
type B = Bool

split (s, t) f = f s t
tt = True
ff = False
o = 0
s = (+1)
cases True s t = s
cases False s t = t
r 0 s t = s
r n s t = t n' (r n' s t)
  where n' = n - 1

---------------------------

z = \n -> r n tt (\n' p -> ff)
p = \n -> r n 0 (\n' q -> n')

mynot = \b -> cases b ff tt

iseven = \n -> r n tt (\n' p -> mynot p)

double = \n -> r n 0 (\n' p -> s (s p))

add = \m n -> r n m (\_ -> s)

eq = \m -> r m z (\_ p n -> r n ff
                   (\n' _ -> p n'))
