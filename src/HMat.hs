{-# LANGUAGE DataKinds, GADTs, AllowAmbiguousTypes, KindSignatures, TypeOperators, ScopedTypeVariables, TypeApplications, InstanceSigs #-}
module HMat where

import Types
import VecOps
import Proofs
import GHC.TypeLits
import Data.List
import Control.Applicative
import Control.Lens hiding (Empty)
import Debug.Trace


transposeMat :: forall m n a. (KnownNat m, KnownNat n) => Mat m n a -> Mat n m a
transposeMat Empty = vRepeat Empty
transposeMat xss
  = splitNat @n
        Empty
        (fmap vHead xss :# transposeMat (fmap vTail xss))

identityM :: forall n a. (KnownNat n, Num a) => Mat n n a
identityM = splitNat @n
                Empty
                (   (1 :# vRepeat 0                  )
                 :# (fmap (0 :#) $ identityM @(n - 1)))

fillMatrix :: forall m n a. (KnownNat m, KnownNat n) => a -> Mat m n a
fillMatrix a = vRepeat (vRepeat a)

scalarMult :: forall m n a. (KnownNat m, KnownNat n, Num a) => a -> Mat m n a -> Mat m n a
scalarMult = fmap . fmap . (*)

addMat :: (KnownNat m, KnownNat n, Num a) => Mat m n a -> Mat m n a -> Mat m n a
addMat = liftA2 (liftA2 (+))

multMat
  :: forall m n n' a. (KnownNat m, KnownNat n, KnownNat n', Num a) => 
     Mat m n  a ->
     Mat n n' a ->
     Mat m n' a
multMat a b = (<$> transposeMat b) . dotProd <$> a

mIndex
  :: forall m n mm nm a. (KnownNat m, KnownNat n, KnownNat mm, KnownNat nm
                         ,CmpNat m mm ~ LT, CmpNat n nm ~ LT) =>
                         Mat mm nm a -> a
mIndex mat = vIndex @n (vIndex @m mat)

unsafeIndexMat :: forall m n a. Mat m n a -> Integer -> Integer -> a
unsafeIndexMat mat m n = unsafeIndexVec (unsafeIndexVec mat m) n

_m :: forall i j m n a. (KnownNat i, KnownNat j
                        , KnownNat m, KnownNat n
                        , CmpNat i m ~ LT, CmpNat j n ~ LT)
                        => Lens' (Vec m (Vec n a)) a
_m = vLens @i . vLens @j

(.#)
  :: forall m n n' a. (KnownNat m, KnownNat n, KnownNat n', Num a) =>
     Mat m n  a ->
     Mat n n' a ->
     Mat m n' a
(.#) = multMat

infixl 7 .#

(+#) :: (KnownNat m, KnownNat n, Num a) => Mat m n a -> Mat m n a -> Mat m n a
(+#) = addMat

infixl 6 +#

(-#) :: (KnownNat m, KnownNat n, Num a) => Mat m n a -> Mat m n a -> Mat m n a
a -# b = a +# (scalarMult (-1) b)

infixl 6 -#


luDecomp :: forall n a. (Num a, KnownNat n, Fractional a, CmpNat 0 n ~ LT) => Mat n n a -> (Mat n n a, Mat n n a)
luDecomp m = let (u, _, l) = normaliseMat @0 m
                in (l, u)

normaliseCorner 
    :: forall i n a. ( Num a, Fractional a
                     , KnownNat n, KnownNat i
                     , CmpNat i n ~ LT)
                     => Mat n n a
                     -> (Mat n n a, Mat n n a, Mat n n a)
normaliseCorner m = let elem = m ^. _m @i @i
                        e  = identityM & _m @i @i .~ (1/elem)
                        e' = identityM & _m @i @i .~ (elem)
                     in (multMat e m, e, e')

normaliseColElem
    :: forall i j n a. ( Num a, Fractional a
                       , KnownNat n, KnownNat i, KnownNat j
                       , CmpNat i n ~ LT, CmpNat j n ~ LT)
                       => Mat n n a
                       -> (Mat n n a, Mat n n a, Mat n n a)
normaliseColElem m = let elem = m ^. _m @i @j
                         e  = identityM & _m @i @j .~ (-elem)
                         e' = identityM & _m @i @j .~ (elem)
                      in (multMat e m, e, e')

normaliseCols
    :: forall i j n a. ( Num a, Fractional a
                       , KnownNat n, KnownNat i, KnownNat j
                       , CmpNat i n ~ LT, CmpNat j n ~ LT)
                       => Mat n n a 
                       -> (Mat n n a, Mat n n a, Mat n n a)
normaliseCols m = let (m', e, ei) = normaliseColElem @i @j m
                   in compareNats @i {- < -} @n
                            (let (m'', e', e'i) = normaliseCols @(i+1) @j m'
                              in (m'', multMat e' e, multMat ei e'i))
                            (m', e, ei)

normaliseMat 
    :: forall i n a. ( Num a, Fractional a
                     , KnownNat n, KnownNat i
                     , CmpNat i n ~ LT)
                     => Mat n n a
                     -> (Mat n n a, Mat n n a, Mat n n a)
normaliseMat m =
    let (m', e, ei) = normaliseCorner @i m
        in compareNats @i {- < -} @n
               (let (m'',  e',  e'i ) = normaliseCols @(i+1) @i m'
                    (m''', e'', e''i) = normaliseMat  @(i+1) m''
                  in (m''', multMat e'' (multMat e' e), multMat ei (multMat e'i e''i)))
               (m', e, ei)
