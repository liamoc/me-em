module ModelChecker.Examples where

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Unit hiding (_≟_)
open import Data.Nat
open import Data.List
open import Data.Product

open import HDec
open import ModelChecker
open import Properties


HiHorse : Diagram ⊤ ℕ
LoRoad  : Diagram ⊤ ℕ
HiHorse = let δ = λ { (ℓ , σ) → [ (ℓ , suc σ )]}
           in td δ tt

LoRoad = let δ = λ { (ℓ , σ) → [ (ℓ , pred σ )]}
          in td δ tt

open CTL (⊤ × ⊤) ℕ

tree = model (HiHorse ∥ LoRoad) 0

reaches10 : HDec _
reaches10 = ef (now (λ ⦃ σ ⦄ → σ ≟ 10)) tree 20

proof : tree ⊧ EF ⟨ (λ ⦃ σ ⦄ → σ ≡ 10) ⟩
proof = di-⊧ (evidence reaches10)
