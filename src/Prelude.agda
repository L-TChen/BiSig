module Prelude where

open import Function                           public
open import Data.Empty                         public
open import Data.Unit.Polymorphic              public
  using (⊤; tt)
open import Data.Nat                           public
  using (ℕ; zero; suc; _+_; _⊔_)
open import Data.Fin                           public
  using (Fin; #_; zero; suc)
open import Data.Fin.Literals                  public
open import Data.List                          public 
  using (List; []; _∷_)
open import Data.List.Membership.Propositional public
open import Data.Product                       public
  using (_×_; _,_; Σ; Σ-syntax; ∃; ∃-syntax; <_,_>)
open import Data.Sum                           public
  using (_⊎_; [_,_])
  renaming (inj₁ to inl; inj₂ to inr)

open import Relation.Nullary                      public
  using (Dec; yes; no; _because_)
open import Relation.Binary                       public
  using (Decidable)
open import Relation.Binary.PropositionalEquality public
  using (_≡_; refl; cong; cong₂)

open import Level
  renaming (suc to lsuc)

variable
  ℓ ℓ₀ ℓ₁ ℓ₂ : Level

infixr -10 _⇒_
_⇒_ : {I : Set} (X : I → Set ℓ₁) (Y : I → Set ℓ₂) → Set _
X ⇒ Y = ∀ {i} → X i → Y i

-- relative continuation monad
record Cont (Val : Set) (n : ℕ) : Set where
  constructor cont
  field runCont : (Fin n → Val) → Val
open Cont public
