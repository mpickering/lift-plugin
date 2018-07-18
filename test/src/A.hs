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

test2_naive = [|| foo ||]

--test3 = p foo1

