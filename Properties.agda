module Properties where
open import Data.Empty
open import Relation.Nullary using (Dec; yes; no; ¬_) public
open import Data.Unit hiding (_≟_ ; _≤_ ;  _≤?_ ; decTotalOrder; total )
open import Data.Product as Prod hiding (map)
open import Function
open import Data.Sum as Sum hiding (map ; [_,_])
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat hiding ( ≤-pred )
open import Relation.Nullary.Decidable using ( ⌊_⌋) public
open import Relation.Nullary.Negation  using ( ¬? ) public
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_)
open import Data.Bool.Properties using (T-∧; T-∨)
open import Data.List.Any hiding (any) renaming (map to map-any)
open import Data.List.All hiding (all) renaming (map to map-all)
open import Data.List as L hiding (any; all; and; or; map)
open import Data.Maybe as M renaming (map to mapMaybe) hiding (Any ; All)
open import Category.Monad
open import Category.Applicative
open import Category.Functor
open import Level hiding (suc ; zero)
import Data.Vec as V
import Data.Stream as S


open import Generators

T? : (b : Bool) → Dec (T b)
T? true = yes tt
T? false = no id

record Property (P : Set) : Set where
  constructor prop
  field found : Bool
  field proof : T found → P

fromDec : ∀{A : Set} → Dec A → Property A
fromDec (yes p) = prop true  (const p)
fromDec (no ¬p) = prop false ⊥-elim

record IsProp (t : Set → Set) : Set₁ where
  field conversion : (∀ {p} → t p → Property p)

instance
  PropertyIsProp : IsProp Property
  PropertyIsProp = record { conversion = id }

  DecIsProp : IsProp Dec
  DecIsProp = record { conversion = fromDec }

open IsProp ⦃ ... ⦄

module Lemmas where
  open import Function.Equivalence using (Equivalence)
  open import Function.Equality using (_⟨$⟩_)

  ∧-T : ∀{a b} → T (a ∧ b) → T a × T b
  ∧-T = _⟨$⟩_ (Equivalence.to T-∧)

  ∨-T : ∀{a b} → T (a ∨ b) → T a ⊎ T b
  ∨-T = _⟨$⟩_ (Equivalence.to T-∨)







is-monad : RawMonad Property
is-monad = record { return = return ; _>>=_ = bind }
  where
    return : ∀{P} → P → Property P
    return = prop true ∘ const

    bind : ∀{P Q} → Property P → (P → Property Q) → Property Q
    bind (prop true p) f = f (p tt )
    bind (prop false p) f = prop false ⊥-elim

is-monad-plus : RawMonadPlus Property
is-monad-plus = record { monadZero = record { monad = is-monad ; ∅ = fail } ; _∣_ = alt } 
  where
    fail : ∀{X} → Property X
    fail = prop false ⊥-elim

    alt : ∀{X} → Property X → Property X → Property X
    alt (prop x p) (prop y q) = prop (x ∨ y) ([ p , q ]′ ∘ Lemmas.∨-T)

open RawMonadPlus is-monad-plus

is-applicative : RawApplicative Property
is-applicative = record { pure = return ; _⊛_ = app }
  where
    app : ∀{A B} → Property (A → B) → Property A → Property B
    app (prop x f) (prop y a)  = prop (x ∧ y) (uncurry _$_ ∘ Prod.map f a ∘ Lemmas.∧-T)

is-functor : RawFunctor Property
is-functor = record { _<$>_ = map }
  where map : ∀ {P Q} → (P → Q) → Property P → Property Q
        map f (prop a p) = prop a (f ∘ p)

search : ∀ {X}{p : X → Set}{prop}
       → ℕ → ⦃ g : Gen X  ⦄
       → ⦃ P : IsProp prop ⦄
       → ((x : X) → prop (p x))
       → Property (∃ p)
search n ⦃ s ⦄ f = V.foldr _ _∣_ ∅
                     (V.map (quantify ∘ conversion ∘ f) (S.take n s))
  where
    quantify : ∀ {X}{p : X → Set}{i}
        → Property (p i) → Property (∃ p)
    quantify (prop a p) = prop a (λ x → _ , p x)

infixl 60 _and_
_and_ : ∀{A B}{prop₁ prop₂}
      → ⦃ P₁ : IsProp prop₁ ⦄ → prop₁ A
      → ⦃ P₂ : IsProp prop₂ ⦄ → prop₂ B
      → Property (A × B)
a and b = _,_ <$> conversion a ⊛ conversion b

_or_ : ∀{A B}{prop₁ prop₂}
     → ⦃ P₁ : IsProp prop₁ ⦄ → prop₁ A
     → ⦃ P₂ : IsProp prop₂ ⦄ → prop₂ B
     → Property (A ⊎ B)
a or b = inj₁ <$> conversion a ∣ inj₂ <$> conversion b

_implies_ : ∀{A B : Set}{prop}
          → Dec A
          → ⦃ P₁ : IsProp prop ⦄ → prop B
          → Property (A → B)
no ¬p implies b = return (⊥-elim ∘ ¬p)
yes p implies b = const <$> conversion b

Ty : ∀ {P} → Property P → Set
Ty {P} (prop true p) = P
Ty (prop false p) = ⊤

Pr :  ∀ {P} → (p : Property P) → Ty p
Pr (prop true p) = p tt
Pr (prop false p) = tt


any : ∀ {X : Set}{p : X → Set}{prop}
    → ⦃ P : IsProp prop ⦄
    → (xs : List X)
    → ((x : X) → prop (p x))
    → Property (Any p xs)
any [] f = ∅
any (x ∷ xs) f = here <$> conversion (f x) ∣ there <$> any xs f

all : ∀ {X : Set}{p : X → Set}{prop}
    → ⦃ P : IsProp prop ⦄
    → (xs : List X)
    → ((x : X) → prop (p x))
    → Property (All p xs)
all [] f = return []
all (x ∷ xs) f = _∷_ <$> conversion (f x) ⊛ all xs f
