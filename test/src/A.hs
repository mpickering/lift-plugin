{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
module A where

import Prelude hiding (Applicative(..))

import Data.Functor.Identity
import Language.Haskell.TH.Syntax

import LiftPlugin

newtype Code a = Code (Q (TExp a))

runCode (Code a) = a

instance Pure Code where
  pure = Code . unsafeTExpCoerce . lift

instance Pure Identity where
  pure = Identity


foo 'a' = 'a'

foo1 x = x

test1 :: Code String
test1 = pure "1"

test2 :: Pure p => p (Char -> Char)
test2 = pure foo

test3 :: Code (Char -> Char)
test3 = test2

test4 :: Identity (Char -> Char)
test4 = test2

test5 :: Pure p => p (a -> a)
test5 = pure foo1

test7 :: Pure p => p (a -> Maybe a)
test7 = pure Just

{-
- - These should all fail
test8 :: Q Exp
test8 = lift id

l :: (a -> a) -> Q Exp
l = lift

test9 :: Q Exp
test9 = l id
-}

--test6 :: Pure p => (a -> a) -> p (a -> a)
--test6 f = pure f

-- This should fail for now but in theory we should accept it as
-- we would accept `pure return <$> pure ()`.
--test6 :: Pure p => p (IO ())
--test6 = pure (return ())

-- This should fail
--test7 :: String
--test7 = show id

test2_naive = [|| foo ||]

test_con = [|| Just ||]

test_foo1 = [|| foo1 ||]

--test3 = pure foo1

ifTest :: Syntax r => r Bool
ifTest = overload (if (pure True) then (pure False) else (pure True))

