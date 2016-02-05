module ModelChecker.Examples where

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Unit hiding (_≟_)
open import Data.Nat
open import Data.List

open import ModelChecker
open import Properties

open import Pair

HiHorse : Diagram ⊤ ℕ
LoRoad  : Diagram ⊤ ℕ
HiHorse = let δ = λ { (ℓ , σ) → [ (ℓ , suc σ )]}
           in td δ tt

LoRoad = let δ = λ { (ℓ , σ) → [ (ℓ , pred σ )]}
          in td δ tt

open CTL (⊤ × ⊤) ℕ

reaches10 : Property _
reaches10 = ef (now (λ ⦃ σ ⦄ → σ ≟ 10))
               (model (HiHorse ∥ LoRoad) 0) 20

proof : model (HiHorse ∥ LoRoad) 0 ⊧ EF ⟨ (λ ⦃ σ ⦄ → σ ≡ 10) ⟩
proof = di-⊧ (Pr reaches10)
