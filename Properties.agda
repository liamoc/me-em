module Properties where
open import Data.Empty
open import Relation.Nullary using (Dec; yes; no; ¬_) public
open import Data.Unit hiding (_≟_ ; _≤_ ;  _≤?_ ; decTotalOrder; total )
open import Data.Product hiding (map)
open import Function
open import Data.Sum hiding (map ; [_,_])
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat hiding ( ≤-pred )
open import Relation.Nullary.Decidable using ( ⌊_⌋) public
open import Relation.Nullary.Negation  using ( ¬? ) public
open import Data.Bool using (Bool; true; false; T)
open import Data.List.Any hiding (any) renaming (map to map-any)
open import Data.List.All hiding (all) renaming (map to map-all)
open import Data.List as L hiding (any; all; and; or)
open import Data.Maybe as M renaming (map to mapMaybe) hiding (Any ; All)
open import Category.Monad
open import Level hiding (suc ; zero)
open RawMonad (M.monad {Level.zero})
open RawMonadPlus (M.monadPlus {Level.zero}) using (_∣_)

_⟨$⟩_ = _<$>_

open import Generators

{- 
-- Relation.Nullary
data Dec (P : Set) : Set where
  yes :   P → Dec P
  no  : ¬ P → Dec P

-- Relation.Nullary.Product
_×-dec_ : ∀{P Q} → Dec P → Dec Q → Dec (P × Q)

-- Relation.Nullary.Sum
_⊎-dec_  : ∀{P Q} → Dec P → Dec Q → Dec (P ⊎ Q)

-- Relation.Nullary.Negation
¬? : ∀{P} → Dec P → Dec (¬ P)

-- Relation.Nullary.Implication
_→-dec_ : ∀{P Q} → Dec P → Dec Q → Dec (P → Q)


-- Data.Nat
_≟_ : (m : ℕ) → (n : ℕ) → Dec (m ≡ n)
zero  ≟ zero   = yes refl
suc m ≟ suc n  with m ≟ n
... | yes p    = yes (cong suc p)
... | no prf   = no (prf ∘ cong pred)
zero  ≟ suc n  = no λ()
suc m ≟ zero   = no λ()

-- Data.Nat
_≤?_ : (m : ℕ) → (n : ℕ) → Dec (m ≤ n)
zero  ≤? _     = yes z≤n
suc m ≤? zero  = no λ()
suc m ≤? suc n with m ≤? n
...            | yes m≤n = yes (s≤s m≤n)
...            | no  m≰n = no  (m≰n ∘ ≤-pred)
  where ≤-pred : ∀ {m n} → suc m ≤ suc n → m ≤ n
        ≤-pred (s≤s m≤n) = m≤n

-}

T? : (b : Bool) → Dec (T b)
T? true = yes tt
T? false = no id


Property = Maybe

decide : ∀ {A : Set} → Dec A → Property A
decide (yes p) = just p
decide (no  _) = nothing

record IsProp (t : Set → Set) : Set₁ where
  field conversion : (∀ {p} → t p → Property p)

instance
  PropertyIsProp : IsProp Property
  PropertyIsProp = record { conversion = id }

  DecIsProp : IsProp Dec
  DecIsProp = record { conversion = decide }

open IsProp ⦃ ... ⦄

_and_ : ∀{A B}{prop₁ prop₂}
      → ⦃ P₁ : IsProp prop₁ ⦄ → prop₁ A
      → ⦃ P₂ : IsProp prop₂ ⦄ → prop₂ B
      → Property (A × B)
a and b = _,_ ⟨$⟩ conversion a ⊛ conversion b

_or_ : ∀{A B}{prop₁ prop₂}
     → ⦃ P₁ : IsProp prop₁ ⦄ → prop₁ A
     → ⦃ P₂ : IsProp prop₂ ⦄ → prop₂ B
     → Property (A ⊎ B)
a or b = (inj₁ ⟨$⟩ conversion a) ∣ (inj₂ ⟨$⟩ conversion b)

_implies_ : ∀{A B : Set}{prop}
          → Dec A
          → ⦃ P₁ : IsProp prop ⦄ → prop B
          → Property (A → B)
no ¬p implies b = just (λ a → ⊥-elim (¬p a))
yes p implies b = (λ x _ → x) ⟨$⟩ (conversion b)

infixl 60 _and_
import Data.Vec as V
import Data.Stream as S

search : ∀ {X}{p : X → Set}{prop}
       → ℕ → ⦃ g : Gen X  ⦄
       → ⦃ P : IsProp prop ⦄
       → ((x : X) → prop (p x))
       → Property (∃ p)
search n ⦃ s ⦄ f =
          V.foldr _ (_∣_) nothing
              (V.map (quantify ∘ conversion ∘ f) (S.take n s))
  where
    quantify : ∀ {X}{p : X → Set}{i}
        → Property (p i) → Property (∃ p)
    quantify p = _,_ _ ⟨$⟩ p


Ty : ∀ {P} → Property P → Set
Ty {P} (just  _) = P
Ty {P} (nothing) = ⊤
Pr :  ∀ {P} → (p : Property P) → Ty p
Pr (just p) = p
Pr (nothing) = tt



any : ∀ {X : Set}{p : X → Set}{prop}
    → ⦃ P : IsProp prop ⦄
    → (xs : List X)
    → ((x : X) → prop (p x))
    → Property (Any p xs)
any [] f = nothing
any (x ∷ xs) f with conversion (f x)
... | just p = just (here p)
... | nothing = mapMaybe there (any xs f)

all : ∀ {X : Set}{p : X → Set}{prop}
    → ⦃ P : IsProp prop ⦄
    → (xs : List X)
    → ((x : X) → prop (p x))
    → Property (All p xs)
all [] f = just []
all (x ∷ xs) f with conversion (f x)
... | just p = mapMaybe (_∷_ p) (all xs f)
... | nothing = nothing

