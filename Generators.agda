module Generators where

open import Coinduction
import Data.Stream as S
import Data.Vec as V
import Data.List.NonEmpty as N
open N hiding (concat; map; [_])
open import Data.List hiding (concat ; sequence ; and ; any ; all)
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Function



Gen = Stream
  where open S

{- 
  -- Data.Stream

  data Stream (A : Set) : Set where
    _∷_ : (x : A) (xs : ∞ (Stream A)) → Stream A
-}

instance nats₀ = S.iterate suc 0

open S using (Stream;_∷_)
open V using (Vec;[];_∷_)

readMulti : ∀{A}{l}
          → Vec (Stream A) l → (Vec A l × Vec (Stream A) l)
readMulti [] = [] , []
readMulti (x ∷ v) with readMulti v
... | as , ss =  (S.head x ∷ as) , (S.tail x ∷ ss)

sequence : ∀{A}{l}
         → Vec (Stream A) l → Stream (Vec A l)
sequence vs with readMulti vs
... | as , ss = as ∷ ♯ sequence ss

concat : ∀ {A} → Stream (List⁺ A) → Stream A
concat ((x ∷ [])     ∷ xss) = x ∷ ♯ concat (♭ xss)
concat ((x ∷ y ∷ xs) ∷ xss) = x ∷ ♯ concat ((y ∷ xs) ∷ xss)

multiplex : ∀{A}{l}
          → Vec (Stream A) (suc l) → Stream A
multiplex vs = concat (S.map fromVec (sequence vs))

instance
  sums : ∀{A}{B}
    → ⦃ a : Gen A ⦄ → ⦃ b : Gen B ⦄ → Gen (A ⊎ B)
  sums ⦃ a ⦄ ⦃ b ⦄ = multiplex
        ( S.map inj₁ a ∷ S.map inj₂ b ∷ [])

Σ-plane : ∀{A}{B : A → Set}
  → Gen A
  → ((x : A) → Gen (B x))
  → Gen (Gen (Σ A B))
Σ-plane as bs = S.map (λ a → S.map (_,_ a) (bs a)) as

zig-zag′ : ∀ {A} → List⁺ A → List⁺ (Stream A) → Stream (Stream A) → Stream A
zig-zag  : ∀ {A} → List⁺ (Stream A) → Stream (Stream A) → Stream A

zig-zag xs xss = zig-zag′ (N.map S.head xs) (N.map S.tail xs) xss

zig-zag′ (x ∷ [])     xss (xs ∷ sxs) = x ∷ ♯ zig-zag (xs ∷ toList xss) (♭ sxs)
zig-zag′ (x ∷ y ∷ xs) xss sxs        = x ∷ ♯ zig-zag′ (y ∷ xs) xss sxs

flat : ∀ {A} → Stream (Stream A) → Stream A
flat (xs ∷ xss) = zig-zag (xs ∷ []) (♭ xss)

_alongside_ : ∀{A}{B : A → Set}
    → Gen A
    → ((x : A) → Gen (B x))
    → Gen (Σ A B)
as alongside bs = flat (Σ-plane as bs)

instance
  products : ∀{A}{B}
     → ⦃ a : Gen A ⦄
     → ⦃ b : Gen B ⦄
     → Gen (A × B)
  products ⦃ a ⦄ ⦃ b ⦄ = a alongside (λ x → b)



vecs : ∀{A}
   → (n : ℕ) → ⦃ g : Gen A ⦄
   → Gen (Vec A n)
vecs zero ⦃ g ⦄ = S.repeat []
vecs (suc n) ⦃ g ⦄ =
  S.map (λ { (a , b) → a ∷ b }) $
    products ⦃ g ⦄ ⦃ vecs n ⦃ g ⦄ ⦄

instance
  lists : ∀{A} → ⦃ g : Gen A ⦄ → Gen (List A)
  lists ⦃ g ⦄ = flat $
    S.map (λ n → S.map V.toList (vecs n)) nats₀
