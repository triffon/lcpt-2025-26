{-# LANGUAGE RankNTypes #-}

applyToBoth :: (forall a. (a -> a)) -> (Int, Bool) -> (Int, Bool)
applyToBoth f (x, y) = (f x, f y)


{-
applyToBoth :: forall a. (a -> a) -> (Int, Bool) -> (Int, Bool)
applyToBoth f (x, y) = (f x, f y)
-}

-- applyToBoth id (42, True) ---> (42, True)
