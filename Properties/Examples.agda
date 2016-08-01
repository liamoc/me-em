module Properties.Examples where

open import Generators
open import HDec
open import Properties

open import Data.Empty
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Data.Nat
open import Data.Nat.GCD
open import Function
open import Data.Product
open import Relation.Binary.PropositionalEquality

_² : ℕ → ℕ
i ² = i * i

infixr 12 _²

triad : Property _
triad = exists $ λ { (x , y , z)
         → ¬? (x ≟ 0) and ¬? (y ≟ 0) and ¬? ((x ² + y ²) ≟ z ²) }

gcd? : ∀ l m n → Dec (GCD l m n)
gcd? l m n with gcd l m
... | d , p with d ≟ n
... | no q = no (λ p′ → q (GCD.unique p p′))
... | yes r = yes (subst (GCD l m) r p)

ex₃ : Property (∃ (λ i → ¬ GCD (i ² + 7) ((i + 1)² + 7) 1))
ex₃ = exists $ λ i →
       ¬? (gcd? (i ² + 7) ((i + 1)² + 7) 1)

TyD : ∀{P} → Dec P → Set
TyD {P} (yes _) = P
TyD {P} (no  _) = ¬ P
PrD :  ∀{P} → (d : Dec P) → TyD d
PrD (yes p) = p
PrD (no  p) = p

ex₁ : 135 ≤ 341
ex₁ = PrD (135 ≤? 341)

ex₂ : GCD 6 35 1
ex₂ = PrD (gcd? 6 35 1)

lemma : ∃ (λ i → ¬ GCD (i ² + 7) ((i + 1)² + 7) 1)
lemma = check 60 ex₃
