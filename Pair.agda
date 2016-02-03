module Pair where

infixr 2 _×_
infixr 4 _,_
record _×_ (A B : Set) : Set where
  no-eta-equality
  constructor _,_
  field fst : A
        snd : B

open _×_ public
