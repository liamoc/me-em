module ModelChecker where

open import Data.Product hiding (map)
open import Data.List hiding (all ; any)
open import Data.List.All as All hiding (map; all)
open import Data.List.Any as Any hiding (map; any)
open import Coinduction
open import Data.Nat
open import Function
open import Relation.Binary.PropositionalEquality

open import HDec


record Diagram (L : Set)(Σ : Set) : Set₁ where
  no-eta-equality
  constructor td
  field  δ : L × Σ → List (L × Σ)
         I : L

_∥_ : ∀{L₁ L₂}{Σ} → Diagram L₁ Σ → Diagram L₂ Σ → Diagram (L₁ × L₂) Σ
(td δ₁ i₁) ∥ (td δ₂ i₂) = td δ (i₁ , i₂)
  where
    δ = (λ { ((ℓ₁ , ℓ₂) , σ) →
      map (λ { (ℓ₁′ , σ′) → (ℓ₁′ , ℓ₂ ) , σ′ }) (δ₁ (ℓ₁ , σ)) ++
      map (λ { (ℓ₂′ , σ′) → (ℓ₁  , ℓ₂′) , σ′ }) (δ₂ (ℓ₂ , σ)) })

module CTL(L Σ : Set) where

 data CT : Set where
   At : (L × Σ) → ∞ (List CT) → CT

 model : Diagram L Σ → Σ → CT
 model (td δ I) σ = follow (I , σ)
   where
    follow    : (L × Σ) → CT
    followAll : List (L × Σ) → List CT
    follow    σ         = At σ (♯ followAll (δ σ))
    followAll (σ ∷ σs)  = follow σ ∷ followAll σs
    followAll []        = []

 Formula = (depth : ℕ) → (tree : CT) → Set

 data _⊧_ (m : CT)(φ : Formula) : Set where
   satisfies : ∀ d₀ → (∀ { d } → d₀ ≤′ d → φ d m) → m ⊧ φ

 record DepthInv (φ : Formula) : Set where
   constructor di
   field proof : (∀{n}{m} → φ n m → φ (suc n) m)

 di-⊧ : ∀{n}{φ}{m} ⦃ d : DepthInv φ ⦄ → φ n m → m ⊧ φ
 di-⊧ {n}{φ}{m} ⦃ di d ⦄ p = satisfies n (λ q → di-≤ p q)
   where
     di-≤ : ∀{n n′} → φ n m → n ≤′ n′ → φ n′ m
     di-≤ p ≤′-refl      = p
     di-≤ p (≤′-step l)  = d (di-≤ p l)

 data True : Formula where
   tt : ∀{n}{m} → True n m
 instance
   True-di : DepthInv True
   True-di = di (const tt)

 data ⟨_⟩ (g : ⦃ σ : Σ ⦄ ⦃ ℓ : L ⦄ → Set) : Formula where
   here : ∀{σ}{ℓ}{ms}{d} → g ⦃ σ ⦄ ⦃ ℓ ⦄ → ⟨ g ⟩ d (At (ℓ , σ) ms)

 instance
   ⟨⟩-di : ∀{p : ⦃ σ : Σ ⦄ ⦃ ℓ : L ⦄ → Set} → DepthInv ⟨ p ⟩
   ⟨⟩-di {p} = di proof
     where
       proof : ∀{n}{m} → ⟨ p ⟩ n m → ⟨ p ⟩ (suc n) m
       proof (here x) = here x

 infixr 21 _∧′_

 data _∧′_ (φ ψ : Formula ) : Formula where
    _,_ : ∀{n}{m} → φ n m → ψ n m → (φ ∧′ ψ) n m

 instance
   ∧′-di : ∀{φ ψ} ⦃ p : DepthInv φ ⦄ ⦃ q : DepthInv ψ ⦄ → DepthInv (φ ∧′ ψ)
   ∧′-di ⦃ di p ⦄ ⦃ di q ⦄ = di λ { (a , b) → p a , q b }

 data A[_U_] (φ ψ : Formula) : Formula where
   here  : ∀{t}{n} → ψ n t → A[ φ U ψ ] (suc n) t
   there : ∀{σ}{ms}{n}
     → φ n (At σ ms)
     → All (A[ φ U ψ ] n) (♭ ms)
     → A[ φ U ψ ] (suc n) (At σ ms)

 instance
   A-di : ∀{φ ψ} ⦃ p : DepthInv φ ⦄ ⦃ q : DepthInv ψ ⦄ → DepthInv A[ φ U ψ ]
   A-di {φ}{ψ} ⦃ di p ⦄ ⦃ di q ⦄ = di prf
     where
       prf : ∀{d}{t} → A[ φ U ψ ] d t → A[ φ U ψ ] (suc d) t
       prf (here x)      = here  (q x)
       prf (there x xs)  = there (p x) (All.map prf xs)

 data E[_U_] (φ ψ : Formula) : Formula where
   here  : ∀{t}{n} → ψ n t → E[ φ U ψ ] (suc n) t
   there : ∀{σ}{ms}{n}
     → φ n (At σ ms)
     → Any (E[ φ U ψ ] n) (♭ ms)
     → E[ φ U ψ ] (suc n) (At σ ms)

 instance
    E-di : ∀{φ ψ} ⦃ p : DepthInv φ ⦄ ⦃ q : DepthInv ψ ⦄ → DepthInv E[ φ U ψ ]
    E-di {φ}{ψ} ⦃ di p ⦄ ⦃ di q ⦄ = di prf
      where
        prf : ∀{d}{t} → E[ φ U ψ ] d t → E[ φ U ψ ] (suc d) t
        prf (here x)      = here  (q x)
        prf (there x xs)  = there (p x) (Any.map prf xs)

 AF EF : Formula → Formula
 AF φ = A[ True U φ ]
 EF φ = E[ True U φ ]

 data Completed : Formula where
   completed : ∀{σ}{n}{ms}
             → ♭ ms ≡ []
             → Completed n (At σ ms)
 instance
   Completed-di : DepthInv Completed
   Completed-di = di prf
     where
       prf : ∀{d}{t} → Completed d t → Completed (suc d) t
       prf (completed p) = completed p

 AG EG : Formula → Formula
 AG  φ = A[  φ U φ ∧′ Completed ]
 EG  φ = E[  φ U φ ∧′ Completed ]

 MC : Formula → Set
 MC φ = (t : CT)(d : ℕ) → HDec (φ d t)

 now : ∀{ g : ⦃ σ : Σ ⦄ → ⦃ ℓ : L ⦄ → Set }{hdec}
     → ⦃ P : IsSearch hdec ⦄
     → (⦃ σ : Σ ⦄ → ⦃ ℓ : L ⦄ → hdec (g ⦃ σ ⦄ ⦃ ℓ ⦄) )
     → MC ⟨ g ⟩
 now p (At (ℓ , σ) ms) _ = (| here (toHDec (p ⦃ σ ⦄ ⦃ ℓ ⦄)) |)

 completed? : MC Completed
 completed? (At σ ms) _ = (| completed (empty? (♭ ms)) |)
  where
    empty? : ∀{X}(n : List X) → HDec (n ≡ [])
    empty? []       = return refl
    empty? (_ ∷ _)  = ∅

 infixr 20 _and′_
 _and′_ : ∀ {φ ψ} → MC φ → MC ψ → MC (φ ∧′ ψ)
 _and′_ a b m n = (| a m n , b m n |)

 a-u : ∀{φ ψ} → MC φ → MC ψ → MC A[ φ U ψ ]
 a-u _   _   _          zero     =  ∅
 a-u p₁  p₂  t@(At σ ms)  (suc n)  =  (| here (p₂ t n) |)
                                   ∣  (| there (p₁ t n) rest |)
    where rest = all (♭ ms) λ m → a-u p₁ p₂ m n

 e-u : ∀{φ ψ} → MC φ → MC ψ → MC E[ φ U ψ ]
 e-u _   _   _            zero     = ∅
 e-u p₁  p₂  t@(At σ ms)  (suc n)  =  (| here (p₂ t n) |)
                                   ∣  (| there (p₁ t n) rest |)
    where rest = any (♭ ms) λ m → e-u p₁ p₂ m n

 ef  : ∀{φ} → MC φ → MC (EF φ)
 af  : ∀{φ} → MC φ → MC (AF φ)
 eg  : ∀{φ} → MC φ → MC (EG φ)
 ag  : ∀{φ} → MC φ → MC (AG φ)

 ef p  = e-u  (λ _ _ → return tt) p
 af p  = a-u  (λ _ _ → return tt) p
 eg p  = e-u  p (p and′ completed?)
 ag p  = a-u  p (p and′ completed?)
    
