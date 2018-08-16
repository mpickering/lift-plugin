{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -dcore-lint #-}
module A where


import Prelude hiding (Applicative(..))

import Data.Functor.Identity
import Language.Haskell.TH.Syntax

import LiftPlugin

default ()

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
ifTest = overload $ if (pure True) then (pure False) else (pure True)

appTest :: Syntax r => r Bool
appTest = overload $ (pure const) (pure True) (pure False)

pureTest :: Syntax r => r (Int)
pureTest = overload $ pure (id 5)

lamTest :: Syntax r => r (a -> a)
lamTest = overload $ \a -> a

-- Test for simple var bind
-- This is a bit trickier as can't easier make a lambda as for a normal
-- FunBind
letTest2 :: Syntax r => r Bool
letTest2 = overload $ let t = pure True
                     in t

-- Test for fun bind
letTest :: Syntax r => r Bool
letTest = overload $ let t x = x
                     in t (pure True)

caseTest :: (Syntax r) => r [a] -> r Bool
caseTest xs = overload $ case xs of
                          [] -> (pure False)
                          (_:_) -> (pure True)

caseProdTest :: (Syntax r) => r (a, b) -> r a
caseProdTest ab = overload $ case ab of
                               (a, b) -> a

power :: Syntax r => Int -> r (Int -> Int)
power n = let r = power (n - 1)
          in overload $ \k -> if (pure (==)) (pure n) (pure 0)
                              then pure 1
                              else (pure (*)) k (r k)

staticPower :: Syntax r => r (Int -> Int -> Int)
staticPower = overload (\n -> \k ->
                          if (pure (==)) (wrap n) (wrap 0)
                                  then pure 1
                                  else (pure (*)) k (staticPower ((pure (-)) n (pure 1))  k))

wrapTest :: Pure r => r (Int -> Int)
wrapTest = wrap id

wrapTest2 :: Pure r => r (Int -> Int)
wrapTest2 =  wrap wrapTest




