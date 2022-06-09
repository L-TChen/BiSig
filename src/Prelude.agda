module Prelude where

open import Function                           public
  hiding (_∋_)
open import Data.Empty                         public
  using () renaming (⊥ to ⊥₀; ⊥-elim to ⊥-elim₀)
open import Data.Empty.Polymorphic             public
  using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic              public
  using (⊤; tt)
open import Data.Nat                           public
  using (ℕ; zero; suc; _+_; _⊔_)
open import Data.Fin                           public
  using (Fin; #_; zero; suc)
open import Data.Fin.Literals                  public
open import Data.List                          public 
  using (List; []; _∷_; _++_; length)
open import Data.Vec                           public
  using (Vec; []; _∷_)
open import Data.String                        public
  using (String)
open import Data.Product                       public
  using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax; <_,_>)
open import Data.Sum                           public
  using (_⊎_; [_,_])
  renaming (inj₁ to inl; inj₂ to inr)

open import Relation.Nullary                      public
  using (Dec; yes; no; _because_; ¬_)
open import Relation.Binary                       public
  using (Decidable)
open import Relation.Binary.PropositionalEquality public
  using (_≡_; refl; cong; cong₂; subst; _≢_)

open import Level                                 public
  using (Level; lift)
  renaming (zero to lzero; suc to lsuc; _⊔_ to lmax)

variable
  ℓ ℓ₀ ℓ₁ ℓ₂ ℓ′ : Level

infixr -10 _⇒₁_ _⇒_
_⇒₁_ : {I : Set ℓ′}
  → (X : I → Set ℓ₁) (Y : I → Set ℓ₂) → Set _
X ⇒₁ Y = ∀ {i} → X i → Y i

_⇒_ : {I : Set ℓ₁} {J : Set ℓ₂}
  → (X : I → J → Set ℓ) (Y : I → J → Set ℓ′) → Set _
X ⇒ Y = ∀ {i j} → X i j → Y i j

data Mode : Set where
  Check Infer : Mode