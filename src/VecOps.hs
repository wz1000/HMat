{-# LANGUAGE DataKinds, GADTs, AllowAmbiguousTypes, KindSignatures, TypeOperators, ScopedTypeVariables, TypeApplications, InstanceSigs, FlexibleInstances #-}
module VecOps where

import Types
import Proofs
import GHC.TypeLits
import GHC.TypeLits.Witnesses
import Data.Proxy
import Control.Lens hiding (Empty)

vLength :: forall (n :: Nat) a. KnownNat n => Vec n a -> Integer
vLength v = reifyNat @n

vHead :: Vec (m+1) a -> a
vHead (x :# xs) = x

vTail :: forall m a. Vec m a -> Vec (m-1) a
vTail (x :# (xs :: Vec n a)) = proofProp1 @m @n xs

appendVec :: forall m n a. (KnownNat m, KnownNat n) => Vec m a -> Vec n a -> Vec (m+n) a
appendVec xs Empty = xs
appendVec Empty ys = ys
appendVec (x :# (xs :: Vec m' a)) (ys :: Vec n a) =
    withNatOp (%+) (Proxy @m') (Proxy @n) $
      proofProp4 @m @m' @n $
        x :# appendVec xs ys


vIndex :: forall (i :: Nat) (n :: Nat) a. (KnownNat i, CmpNat i n ~ 'LT) => Vec n a -> a
vIndex (x :# (xs :: Vec n1 a)) = splitNat @i
                                    x
                                    (proofProp3 @n @n1 @i $ vIndex @(i-1) xs)

dotProd :: (KnownNat n, Num a) => Vec n a -> Vec n a -> a
dotProd v1 v2 = sum $ (*) <$> v1 <*> v2

unsafeIndexVec :: forall n a. Vec n a -> Integer -> a
unsafeIndexVec Empty _ = error "index too large"
unsafeIndexVec (x :# _) 0 = x
unsafeIndexVec (_ :# xs) n = unsafeIndexVec xs (n-1)

setVElem :: forall i n a. (KnownNat n, KnownNat i, CmpNat i n ~ LT) => Vec n a -> a -> Vec n a
setVElem (x :# (xs :: Vec n1 a)) x' = splitNat @i
                                        (x' :# xs)
                                        (proofProp3 @n @n1 @i $ x :# (setVElem @(i-1) xs x'))

vLens :: forall i n a. (KnownNat i, KnownNat n, CmpNat i n ~ LT) => Lens' (Vec n a) a
vLens = lens (vIndex @i) (setVElem @i)

_v :: forall i n a. (KnownNat i, KnownNat n, CmpNat i n ~ LT) => Lens' (Vec n a) a
_v = vLens @i

