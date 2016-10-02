{-# LANGUAGE DataKinds, GADTs, AllowAmbiguousTypes, KindSignatures, TypeOperators, ScopedTypeVariables, TypeApplications, InstanceSigs, FlexibleInstances #-}
module Types (
  Vec(..),
  Mat(..),
  matFromList,
  vRepeat,
  reifyNat
    ) where

import Proofs
import Data.List (intercalate)
import GHC.TypeLits
import Data.Monoid ((<>))
import Data.Foldable (toList)

data Vec (n :: Nat) a where
    Empty :: Vec 0 a
    (:#) :: KnownNat n => a -> Vec n a -> Vec (n+1) a

infixr 5 :#

instance Functor (Vec n) where
    fmap f Empty = Empty
    fmap f (x :# xs) = f x :# fmap f xs

instance Foldable (Vec n) where
    foldMap f Empty = mempty
    foldMap f (x :# xs) = f x <> foldMap f xs

instance Traversable (Vec n) where
    traverse f Empty = pure Empty
    traverse f (x :# xs) = (:#) <$> f x <*> traverse f xs

instance KnownNat n => Applicative (Vec n) where
    pure x = vRepeat x
    (<*>) :: Vec n (a->b) -> Vec n a -> Vec n b
    Empty <*> Empty = Empty
    (f :# (fs :: Vec n1 (a->b))) <*> (x :# (xs :: Vec n2 a)) =
             proofProp2 @n1 @n2 
                $ f x :# (fs <*> xs)

instance Show a => Show (Vec m (Vec n a)) where
    show = showMat

type Mat m n a = Vec m (Vec n a)

showVec :: Show a => Vec n a -> String
showVec Empty = ""
showVec (x :# xs) = show x ++ "\t" ++ showVec xs

showMat :: Show a => Mat m n a -> String
showMat = ("\n" ++) . (++ "\n") . intercalate "\n" . map (\x -> "[" ++ x ++ "]") . map showVec . toList

vecFromList :: forall n a. KnownNat n => [a] -> Vec n a
vecFromList xs = splitNat @n
                    Empty
                    (case xs of
                            (x:xs) -> x :# (vecFromList @(n-1) xs))

matFromList :: forall m n a. (KnownNat m, KnownNat n) => [[a]] -> Mat m n a
matFromList = vecFromList . map vecFromList

vRepeat :: forall n a. (KnownNat n) => a -> Vec n a
vRepeat a = splitNat @n
                Empty
                (a :# vRepeat @(n-1) a)
