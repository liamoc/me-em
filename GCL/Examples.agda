module GCL.Examples where

open import Data.Nat
open import Data.Bool hiding (_≟_)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.List hiding (and; or)

import Data.Stream as S

open import Properties
open import Generators
open import ModelChecker

record State : Set where
  field
    intent₁ : Bool
    intent₂ : Bool
    turn    : ℕ
    inCS₁   : Bool
    inCS₂   : Bool

initialState : State
initialState = record
  { inCS₁ = false
  ; inCS₂ = false
  ; intent₁ = false
  ; intent₂ = false
  ; turn = 0
  }

open State ⦃ ... ⦄

open import GCL State

open CTL (GCL × GCL) State

CS₁ : GCL
CS₁ =
    update (λ σ → record σ { inCS₁ = true  }) ·
    skip ·
    update (λ σ → record σ { inCS₁ = false })

CS₂ : GCL
CS₂ =
    update (λ σ → record σ { inCS₂ = true  }) ·
    skip ·
    update (λ σ → record σ { inCS₂ = false })


petersons₁ : GCL
petersons₁ =
   update (λ σ → record σ { intent₁ = true }) ·
   update (λ σ → record σ { turn = 0 }) ·
   await (not intent₂ ∨ ⌊ turn ≟ 1 ⌋) ·
   CS₁ ·
   update (λ σ → record σ {intent₁ = false })
petersons₂ : GCL
petersons₂ =
   update (λ σ → record σ { intent₂ = true }) ·
   update (λ σ → record σ { turn = 1 }) ·
   await (not intent₁ ∨ ⌊ turn ≟ 0 ⌋) ·
   CS₂ ·
   update (λ σ → record σ {intent₂ = false })

petersons = ⟦ petersons₁ ⟧ ∥ ⟦ petersons₂ ⟧

Termination : Formula
Termination = AF ⟨ allSkip ⟩
  where
    allSkip : ⦃ ℓ : GCL × GCL ⦄ → Set
    allSkip ⦃ ℓ = (a , b) ⦄ = a ≡ skip × b ≡ skip

Mutex : Formula
Mutex = AG ⟨ T (not (inCS₁ ∧ inCS₂)) ⟩

SF : Formula
SF =  AF ⟨ T inCS₁ ⟩ ∧′ AF ⟨ T inCS₂ ⟩

termination? : ∀ m n → Property (Termination n m)
termination? = af (now (skip? _ and skip? _))

mutex? : ∀ m n → Property (Mutex n m)
mutex? = ag (now (T? _))

sf? : ∀ m n → Property (SF n m)
sf? = and′ (af (now (T? _))) (af (now (T? _)))

abstract
  petersons-search : Property (∃ (λ d → (Mutex ∧′ SF ∧′ Termination ) d (model petersons initialState)))
  petersons-search
   = (_,_ 25) ⟨$⟩
       and′ mutex? (and′ sf? termination?)
       (model petersons initialState) 25

  petersons-proof : ∃ (λ d → (Mutex ∧′ SF ∧′ Termination ) d (model petersons initialState))
  petersons-proof = Pr petersons-search


petersons-correct : model petersons initialState ⊧ Mutex ∧′ SF ∧′ Termination
petersons-correct = di-⊧ (proj₂ petersons-proof)




dekkers₁ : GCL
dekkers₁ =
  update (λ σ → record σ { intent₁ = true }) ·
  while intent₂ (
    if ⌊ turn ≟ 0 ⌋ ⟶ skip
    ∷  ⌊ turn ≟ 1 ⌋ ⟶ (
      update (λ σ → record σ { intent₁ = false }) ·
      await (⌊ (turn ≟ 0) ⌋) ·
      update (λ σ → record σ { intent₁ = true }))
    ∷ []
    fi) ·
  CS₁ ·
  update (λ σ → record σ { turn = 1 }) ·
  update (λ σ → record σ { intent₁ = false})

dekkers₂ : GCL
dekkers₂ =
  update (λ σ → record σ { intent₂ = true }) ·
  while (intent₁) (
    if ⌊ turn ≟ 1 ⌋ ⟶ skip
    ∷  ⌊ turn ≟ 0 ⌋ ⟶ (
      update (λ σ → record σ { intent₂ = false }) ·
      await ⌊ turn ≟ 1 ⌋ ·
      update (λ σ → record σ { intent₂ = true }))
    ∷ []
    fi) ·
  CS₂ ·
  update (λ σ → record σ { turn = 0 }) ·
  update (λ σ → record σ { intent₂ = false})

dekkers = ⟦ dekkers₁ ⟧ ∥ ⟦ dekkers₂ ⟧

dekkers-check : Property _
dekkers-check = af (now (T? (inCS₁ ∧ inCS₂))) (model dekkers initialState) 100

