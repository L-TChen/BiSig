open import Prelude

import Syntax.Simple.Description as S
open import Syntax.BiTyped.Description as B

module Language.ModeCorrectness {SD : S.Desc}
  (Id : Set) (_≟Id_ : (x y : Id) → Dec (x ≡ y)) (D : Desc {SD}) where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tm₀ to T; _≟_ to _≟T_)

open import Syntax.NamedContext Id
open import Syntax.NamedContext.Decidable _≟Id_


open import Syntax.BiTyped.Raw.Functor       {SD} Id as R
open import Syntax.BiTyped.Extrinsic.Functor {SD} Id D as E

open import Syntax.BiTyped.Raw.Term          {SD} Id D
open import Syntax.BiTyped.Extrinsic.Term    {SD} Id D

import Data.Vec as V

private variable
  Ξ     : ℕ
  A B   : T
  Γ     : Context T
  AD    : ArgsD Ξ
  σ σ₁ σ₂ : Sub₀ Ξ
  m   : Mode
  t   : Raw m

data SnocView {A : Set ℓ} : List A → Set ℓ where
  nil  : SnocView ∅
  snoc : ∀ xs x → SnocView (xs ++ x ∙ ∅)

snocView : {A : Set ℓ} (xs : List A) → SnocView xs
snocView ∅        = nil
snocView (x ∙ xs) with snocView xs
... | nil       = {!   !}
... | snoc xs z = snoc (x ∙ xs) z



mutual
  synthesize
    : (Γ : Context T) (t : Raw⇉)
    → Dec (∃[ A ] Γ ⊢ t ⇉ A)
  synthesize Γ (` x)   with lookup Γ x
  ... | no ¬p       = no λ where (A , ⊢` x∈) → ¬p (A , x∈)
  ... | yes (A , x) = yes (A , ⊢` x)
  synthesize Γ (t ⦂ A) with inherit Γ t A
  ... | no ¬p = no λ where (B , ⊢⦂ ⊢t) → ¬p ⊢t
  ... | yes p = yes (A , ⊢⦂ p)
  synthesize Γ (op (_ , i , ts))  = {!   !}

  inherit
    : (Γ : Context T) (t : Raw⇇) (A : T)
    → Dec (Γ ⊢ t ⇇ A)
  inherit Γ (t ↑)  A with synthesize  Γ t
  ... | no ¬p = no λ where (⊢⇉ ⊢t refl) → ¬p (A , ⊢t)
  ... | yes (B , ⊢t) with B ≟T A
  ... | no ¬q = no λ where (⊢⇉ ⊢u refl) → ¬q {!   !} -- (uniq-⊢ ⊢t ⊢u)
  ... | yes A=B = yes (⊢⇉ ⊢t A=B)
  inherit Γ (op (_ , i , ts)) A = {!   !}
