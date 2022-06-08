open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Predicate.Term {SD : S.Desc} (D : B.Desc {SD}) (Id : Set) where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tm₀ to T)

open import Syntax.NamedContext Id

open import Syntax.BiTyped.Predicate.Functor {SD} D Id
import Syntax.BiTyped.Raw.Functor {SD} Id as R
open import Syntax.BiTyped.Raw.Term          D Id

private variable
  Ξ   : ℕ
  m   : Mode
  Γ   : Context T
  x y : Id
  A B : T
  t u : Raw m

mutual
  ⊢⇆ : Fam₀
  ⊢⇆ A Γ Check t = Γ ⊢ t ⇇ A
  ⊢⇆ A Γ Infer t = Γ ⊢ t ⇉ A

  data _⊢_⇉_ : Context T → Raw Infer → T → Set where
    ⊢`
      : Γ ∋ x ⦂ A
      → Γ ⊢ ` x ⇉ A
    ⊢∈
      : Γ ⊢ t ⇇ A
      → Γ ⊢ t ∈ A ⇉ A  
    op⇉
      : (t : (R.⟦ D ⟧ Raw) Infer)
      → (⟦ D ⟧ ⊢⇆) A Γ Infer t 
      → Γ ⊢ op t ⇉ A
  data _⊢_⇇_ : Context T → Raw Check → T → Set where
    ⊢⇇
      : Γ ⊢ t ⇉ A
      → A ≡ B
      → Γ ⊢ t ↑ ⇇ B
    op⇇
      : (t : (R.⟦ D ⟧ Raw) Check)
      → (⟦ D ⟧ ⊢⇆) A Γ Check t
      → Γ ⊢ op t ⇇ A
