{-# LANGUAGE DataKinds, GADTs, AllowAmbiguousTypes, KindSignatures, TypeOperators, ScopedTypeVariables, TypeApplications, FlexibleContexts, InstanceSigs, RankNTypes #-}
module Proofs where

import GHC.TypeLits
import Unsafe.Coerce
import Data.Type.Equality
import GHC.TypeLits.Witnesses
import GHC.TypeLits.Compare
import Data.Proxy

reifyNat :: forall (n :: Nat). KnownNat n => Integer
reifyNat = natVal (Proxy :: Proxy n)

proveAdditiveInverse :: forall n m a. KnownNat n => ((((n-m)+m) ~ n) => a) -> a
proveAdditiveInverse a = case unsafeCoerce Refl :: (((n-m)+m) :~: n) of
                              Refl -> a

-- Proof for (m = n+1) => (n = m-1)
proofProp1 :: forall m n a. (m ~ (n+1)) => ((n ~ (m-1)) => a) -> a
proofProp1 a = case unsafeCoerce Refl :: (n :~: (m-1)) of
                    Refl -> a

-- Proof for (m + 1 = n +1) => (m = n)
proofProp2 :: forall m n a. (m+1) ~ (n+1) => ((n ~ m) => a) -> a
proofProp2 a = case unsafeCoerce Refl :: (n :~: m) of
                    Refl -> a

-- Proof that if n < m, and m = m'+1, n-1 < m'
proofProp3 :: forall m m' n a. (m ~ (m'+1), CmpNat n m ~ 'LT) => ((CmpNat (n-1) m' ~ LT) => a) -> a
proofProp3 a = case unsafeCoerce Refl :: (CmpNat (n-1) m' :~: LT) of
                    Refl -> a

-- Proof that if m = m'+1 then (m'+n)+1 = m + n
proofProp4 :: forall m m' n a. m ~ (m'+1) => (((m'+n)+1) ~ (m+n) => a) -> a
proofProp4 a = case unsafeCoerce Refl :: (((m'+ n)+1) :~: (m+n)) of
                    Refl -> a


-- Proof that if n>0 and n is a KnownNat, n-1 is KnownNat
proofPredKnownNat :: forall n a. (KnownNat n, CmpNat n 0 ~ GT) => (KnownNat (n-1) => a) -> a
proofPredKnownNat a = withNatOp (%-) (Proxy @n) (Proxy @1) a

ifNatEQZero :: forall n a. KnownNat n => ((n ~ 0) => a) -> ((CmpNat n 0 ~ GT) => a) -> a
ifNatEQZero true false = case cmpNat (Proxy @n) (Proxy @0) of
                    CEQ x -> case unsafeCoerce Refl :: n :~: 0 of
                             Refl -> true
                    CGT Refl -> false
                    CLT _ -> error "Not possible"

compareNats 
    :: forall n m a. (KnownNat m, KnownNat n) 
       => (((CmpNat (n+1) m ~ LT, KnownNat (n+1)) => a)) 
       -> a
       -> a
compareNats true false
    = withNatOp (%+) (Proxy @n) (Proxy @1) $
        case cmpNat (Proxy @(n+1)) (Proxy @m) of
          CEQ x -> false
          CGT x -> false
          CLT x -> case unsafeCoerce Refl :: CmpNat (n+1) m :~: LT of
                        Refl -> true


-- Helper Method to decompose a type level nat and provide some convienient proofs
splitNat 
  :: forall n a. KnownNat n => ((n ~ 0) => a) -> ((KnownNat (n-1), ((n-1)+1) ~ n) => a) -> a
splitNat true false = ifNatEQZero @n
                            true
                            (proofPredKnownNat @n 
                                $ proveAdditiveInverse @n @1
                                    $ false)
                                
