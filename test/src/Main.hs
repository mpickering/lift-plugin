{-# LANGUAGE TemplateHaskell #-}
module Main(main) where

import A
import LiftPlugin
import Data.Functor.Identity

main = do
  print ($$(runCode test3) 'a')
  print ((runIdentity test4) 'a')
  print (just 'a')
  print (qux 'a')



just :: a -> Maybe a
just = $$(runCode test7)


qux :: a -> a
qux = $$(runCode test5)
