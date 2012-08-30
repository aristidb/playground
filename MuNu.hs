{-# LANGUAGE RankNTypes, ExistentialQuantification #-}

newtype Mu f = Mu (forall a. (f a -> a) -> a)

data Nu f = forall a. Nu a (a -> f a)

newtype Fix f = Fix (f (Fix f))

mu2nu :: Functor f => Mu f -> Nu f
mu2nu (Mu f) = undefined

nu2mu :: Functor f => Nu f -> Mu f
nu2mu (Nu x f) = undefined

mu2fix :: Functor f => Mu f -> Fix f
mu2fix = undefined

nu2fix :: Functor f => Nu f -> Fix f
nu2fix = undefined
