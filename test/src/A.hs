{-# LANGUAGE TemplateHaskell #-}
module A where


import LiftPlugin

foo 'a' = 'a'

foo1 x = x

test1 :: Code String
test1 = p "1"

test2 :: Ops p => p (Char -> Char)
test2 = p foo

test3 :: Code (Char -> Char)
test3 = test2

test4 :: Identity (Char -> Char)
test4 = test2

test5 :: Ops p => p (a -> a)
test5 = p foo1

-- This should fail for now but in theory we should accept it as
-- we would accept `pure return <$> pure ()`.
--test6 :: Ops p => p (IO ())
--test6 = p (return ())

-- This should fail
--test7 :: String
--test7 = show id

test2_naive = [|| foo ||]

--test3 = p foo1

