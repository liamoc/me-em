module HDec where

open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Relation.Nullary
open import Function
open import Data.Sum
open import Data.Product
open import Category.Applicative using (RawApplicative)         public
open import Category.Functor     using (RawFunctor)             public
open import Category.Monad       using (RawMonad; RawMonadPlus) public
open import Data.List.Any        hiding (any)
open import Data.List.All        hiding (all)
open import Data.List            hiding (any; all)

record HDec (P : Set) : Set where
  constructor hd
  field
    found : Bool
    proof : T found → P

HDecType : ∀{P} → HDec P → Set
HDecType {P} (hd found proof) = if found then P else ⊤

evidence : ∀{P} → (h : HDec P) → HDecType h
evidence (hd false proof) = tt
evidence (hd true  proof) = proof tt

fromDec  : ∀{P} → Dec P → HDec P
fromDec (yes p) = hd true (const p)
fromDec (no ¬p) = hd false ⊥-elim

fromDec¬ : ∀{P} → Dec P → HDec (¬ P)
fromDec¬ (yes p) = hd false const
fromDec¬ (no ¬p) = hd true (const ¬p)

record IsSearch (t : Set → Set) : Set₁ where
  constructor is-hdec
  field toHDec : (∀ {p} → t p → HDec p)

instance
  HDecIsSearch : IsSearch HDec
  DecIsSearch  : IsSearch Dec
  HDecIsSearch = is-hdec id
  DecIsSearch  = is-hdec fromDec

open IsSearch ⦃ ... ⦄ public


∨-T : ∀{a b} → T (a ∨ b) → T a ⊎ T b
∨-T = apply (Equivalence.to T-∨)
  where
    open import Function.Equality renaming (_⟨$⟩_ to apply)
    open import Function.Equivalence using (Equivalence)
    open import Data.Bool.Properties

∧-T : ∀{a b} → T (a ∧ b) → T a × T b
∧-T = apply (Equivalence.to T-∧)
  where
    open import Function.Equality renaming (_⟨$⟩_ to apply)
    open import Function.Equivalence using (Equivalence)
    open import Data.Bool.Properties


instance
  hdec-applicative : RawApplicative HDec
  hdec-applicative = record { pure = hd true ∘ const ; _⊛_ = ap }
    where
      ap : ∀{A B : Set} → HDec (A → B) → HDec A → HDec B
      ap {A}{B} (hd found₁ proof₁) (hd found₂ proof₂) = hd (found₁ ∧ found₂) (conclude ∘ ∧-T)
        where
          conclude : T found₁ × T found₂ → B
          conclude (a , b) = proof₁ a (proof₂ b)

instance
  hdec-monad : RawMonad HDec
  hdec-monad = record { return = hd true ∘ const ; _>>=_ = bind }
    where
      bind : ∀{A B : Set} → HDec A → (A → HDec B) → HDec B
      bind (hd false proof) f = hd false ⊥-elim
      bind (hd true  proof) f = f (proof tt)

instance
  hdec-alternative : RawMonadPlus HDec
  hdec-alternative = record { monadZero = record { monad = hdec-monad ; ∅ = empty } ; _∣_ = try }
    where
      empty : ∀{P} → HDec P
      empty = hd false (λ ())

      try : ∀{P} → HDec P → HDec P → HDec P
      try {P} (hd found₁ proof₁) (hd found₂ proof₂) = hd (found₁ ∨ found₂) (choose ∘ ∨-T)
        where
          choose : T found₁ ⊎ T found₂ → P
          choose (inj₁ x) = proof₁ x
          choose (inj₂ y) = proof₂ y

open RawMonadPlus ⦃ ... ⦄ public

_<*>_ = _⊛_

instance
  hdec-functor : RawFunctor HDec
  hdec-functor = record { _<$>_ = λ x y → pure x ⊛ y }

infixr 20 _and_ 
infixr 20 _or_ 

_and_ : ∀{A B}{hdec₁ hdec₂}
      → ⦃ P₁ : IsSearch hdec₁ ⦄ → hdec₁ A
      → ⦃ P₂ : IsSearch hdec₂ ⦄ → hdec₂ B
      → HDec (A × B)
a and b = (| toHDec a , toHDec b |)


_or_ : ∀{A B}{hdec₁ hdec₂}
     → ⦃ P₁ : IsSearch hdec₁ ⦄ → hdec₁ A
     → ⦃ P₂ : IsSearch hdec₂ ⦄ → hdec₂ B
     → HDec (A ⊎ B)
a or b = (| inj₁ (toHDec a) |)
       ∣ (| inj₂ (toHDec b) |)

impl : ∀{A B}{hdec₁ hdec₂}
     → ⦃ P₁ : IsSearch hdec₁ ⦄ → hdec₁ (¬ A)
     → ⦃ P₂ : IsSearch hdec₂ ⦄ → hdec₂ B
     → HDec (A → B)
impl a b = (| contr (toHDec a) |)
         ∣ (| const (toHDec b) |)
  where
    contr : ∀{A B : Set} → ¬ A → A → B
    contr p x = ⊥-elim (p x)


any : ∀{X : Set}{p : X → Set}{hdec}
    → ⦃ P : IsSearch hdec ⦄
    → (xs : List X)
    → ((x : X) → hdec (p x))
    → HDec (Any p xs)
any []       f = ∅
any (x ∷ xs) f = (| here  (toHDec (f x)) |)
               ∣ (| there (any xs f)     |)


all : ∀{X : Set}{p : X → Set}{hdec}
    → ⦃ P : IsSearch hdec ⦄
    → (xs : List X)
    → ((x : X) → hdec (p x))
    → HDec (All p xs)
all []       f = pure []
all (x ∷ xs) f = (| (toHDec (f x)) ∷ (all xs f) |)


T? : ∀ b → Dec (T b)
T? false = no  id
T? true  = yes tt
