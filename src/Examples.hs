{-# LANGUAGE DataKinds, GADTs, AllowAmbiguousTypes, KindSignatures, TypeOperators, ScopedTypeVariables, TypeApplications, InstanceSigs, FlexibleInstances #-}
module Examples where

import GHC.TypeLits
import Types
import VecOps
import HMat
import Control.Lens hiding (Empty)

example :: Mat 3 2 Double
example = (1 :# 2 :# Empty)
       :# (3 :# 4 :# Empty)
       :# (5 :# 6 :# Empty)
       :# Empty

example1 :: Mat 2 3 Double
example1 = matFromList $
    [[1,2,3]
    ,[4,5,6]]

example2 :: Mat 3 2 Double
example2 = matFromList $
    [[7 , 8]
    ,[9 ,10]
    ,[11,12]]

example3 :: Mat 5 5 Double
example3 = identityM

example4 :: Mat 3 3 Double
example4 = matFromList $
    [[1,2,3]
    ,[4,5,6]
    ,[7,8,9]]

example5 :: Mat 3 3 Double
example5 = matFromList $
    [[1,2,2]
    ,[2,2,2]
    ,[2,2,1]]

example6 :: (Mat 3 3 Double, Mat 3 3 Double)
example6 = luDecomp example5

example7 :: Mat 3 3 Double
example7 = (example4+#identityM).#example5

example8 :: Double
example8 = example7 ^. _m @1 @1

example9 =  example1 .# example2
