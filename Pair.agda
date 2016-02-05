module Pair where

infixr 2 _×_
infixr 4 _,_
record _×_ (A B : Set) : Set where
  no-eta-equality
  constructor _,_
  field fst : A
        snd : B

open _×_ public

map : ∀{A B C D} → (A → B) → (C → D) → (A × C → B × D)
map f g (a , b) = f a , g b
