{-# LANGUAGE RankNTypes #-}

applyToBoth :: (forall a. (a -> a)) -> (Int, Bool) -> (Int, Bool)
applyToBoth f (x, y) = (f x, f y)


{-
applyToBoth :: forall a. (a -> a) -> (Int, Bool) -> (Int, Bool)
applyToBoth f (x, y) = (f x, f y)
-}

-- applyToBoth id (42, True) ---> (42, True)

pickFromMatrix :: (forall a. ([a] -> a)) -> [[a]] -> a
pickFromMatrix f l = f (f l)

-- pickFromMatrix head  [[1,2,3],[4,5,6],[7,8,9]] ---> 1
-- pickFromMatrix last  [[1,2,3],[4,5,6],[7,8,9]] ---> 9
-- pickFromMatrix (!!1) [[1,2,3],[4,5,6],[7,8,9]] ---> 5
