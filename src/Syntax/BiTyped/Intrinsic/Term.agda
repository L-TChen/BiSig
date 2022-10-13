open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as T

module Syntax.BiTyped.Intrinsic.Term {SD : S.Desc} (D : T.Desc {SD}) where

open import Syntax.Simple.Term SD
  using () renaming (Tm to TExp; Sub to TSub)
open import Syntax.Context SD
open T {SD}
open import Syntax.BiTyped.Intrinsic.Functor {SD}

private
  variable
    mod   : Mode
    n m   : ℕ
    σ     : TSub n m
    A B C : TExp n
    Γ Δ   : Cxt n

infix 9 `_

data Tm (m : ℕ) : Fam₀ m where
  `_ : _∈_ ⇒ Tm m Infer
  _∋_
    : (A : TExp m) (t : Tm m Check A Γ)
    → Tm m Infer A Γ
  ⇉_by_ : (t : Tm m Infer A Γ) (eq : A ≡ B)
    → Tm m Check B Γ
  op : (⟦ D ⟧ Tm m) mod ⇒ Tm m mod

Tm⇉ Tm⇇ : (m : ℕ) → _
Tm⇉ m = Tm m Infer
Tm⇇ m = Tm m Check

mutual
  rename : Ren Γ Δ 
    → Tm m mod A Γ → Tm m mod A Δ
  rename f (`  x)                        = ` f x
  rename f (A ∋ t)                       = A ∋ rename f t
  rename f (⇉ t by eq)                   = ⇉ rename f t by eq
  rename f (op (D , x , p , σ , q , ts)) =
    op (D , x , p , σ , q , renameMap _ f ts)

  renameMap : (D : ArgsD n)
    → Ren Γ Δ
    → (⟦ D ⟧ᵃˢ Tm m) σ Γ → (⟦ D ⟧ᵃˢ Tm m) σ Δ
  renameMap ∅                 f _        = _
  renameMap (Θ ⊢[ _ ] _ ∙ Ds) f (t , ts) = renameMapᵃ Θ f t , renameMap Ds f ts

  renameMapᵃ : (Θ : List (TExp n))
    → Ren Γ Δ
    → (⟦ Θ ⟧ᵃ Tm m mod A) σ Γ → (⟦ Θ ⟧ᵃ Tm m mod A) σ Δ
  renameMapᵃ ∅       f t = rename f t
  renameMapᵃ (A ∙ Δ) f t = renameMapᵃ Δ (ext f) t

infixr 5 ⟨_⟩_
⟨_⟩_ : Ren Γ Δ
  → ∀ {A} → Tm m mod A Γ → Tm m mod A Δ
⟨ f ⟩ t = rename f t

Sub : (Γ Δ : Cxt m) → Set
Sub Γ Δ = ∀ {A} (x : A ∈ Γ) → Tm _ Infer A Δ

exts : Sub Γ Δ → Sub (A ∙ Γ) (A ∙ Δ)
exts f (here px) = ` here px
exts f (there x) = rename there (f x)

extsⁿ : {Ξ : Cxt m}
  → Sub Γ Δ → Sub (Ξ ++ Γ) (Ξ ++ Δ)
extsⁿ {Ξ = ∅}     f x         = f x
extsⁿ {Ξ = A ∙ Ξ} f (here px) = ` here px
extsⁿ {Ξ = A ∙ Ξ} f (there x) = rename there (extsⁿ f x)

mutual
  sub : Sub Γ Δ
    → ∀ {A} → Tm m mod A Γ → Tm m mod A Δ
  sub f (` x)                         = f x
  sub f (A ∋ t)                       = A ∋ sub f t
  sub f (⇉ t by eq)                   = ⇉ (sub f t) by eq
  sub f (op (D , x , p , σ , q , ts)) =
    op (D , x , p , σ , q , subMap _ f ts)

  subMap : (D : ArgsD n)
    → Sub Γ Δ
    → (⟦ D ⟧ᵃˢ Tm m) σ Γ → (⟦ D ⟧ᵃˢ Tm m) σ Δ
  subMap ∅        f _        = _
  subMap (Θ ⊢[ _ ] _ ∙ Ds) f (t , ts) = subMapᵃ Θ f t , subMap Ds f ts

  subMapᵃ : (Θ : List (TExp n))
    → Sub Γ Δ
    → (⟦ Θ ⟧ᵃ Tm m mod A) σ Γ → (⟦ Θ ⟧ᵃ Tm m mod A) σ Δ
  subMapᵃ ∅       f t = sub f t
  subMapᵃ (A ∙ Δ) f t = subMapᵃ Δ (exts f) t

infixr 5 ⟪_⟫_
⟪_⟫_ : Sub Γ Δ
  → ∀ {A} → Tm m mod A Γ → Tm m mod A Δ
⟪ f ⟫ t = sub f t

module _ {X : Fam m ℓ} (α : (D -Alg) X) where mutual
  fold : Tm m mod ⇒ X mod
  fold (` x)         = α .var x
  fold (A ∋ t)       = α .toInfer (fold t)
  fold (⇉ t by refl) = α .toCheck (fold t)
  fold (op (D , x , p , σ , q , ts)) = α .alg (D , x , p , σ , q , foldMap (ConD.args D) ts)

  foldMap : (D : ArgsD n)
    → (⟦ D ⟧ᵃˢ Tm m) σ ⇒₁ (⟦ D ⟧ᵃˢ X) σ
  foldMap ∅        _        = _
  foldMap (Θ ⊢[ _ ] _ ∙ Ds) (t , ts) = foldMapᵃ Θ t , foldMap Ds ts

  foldMapᵃ : (Θ : List (TExp n))
    → (⟦ Θ ⟧ᵃ Tm m mod A) σ ⇒₁ (⟦ Θ ⟧ᵃ X mod A) σ
  foldMapᵃ ∅       t = fold t
  foldMapᵃ (A ∙ Δ) t = foldMapᵃ Δ t
