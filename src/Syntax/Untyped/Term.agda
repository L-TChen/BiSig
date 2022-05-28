open import Prelude
open import Syntax.Untyped.Signature

module Syntax.Untyped.Term {O : Set} (s : Sig O) where

private
  variable
    n m : ℕ

infix 40 `_

data Tm : ℕ → Set where
  `_ : Fin      ⇒ Tm
  op : ⟦ s ⟧ Tm ⇒ Tm

Ren : (n m : ℕ) → Set
Ren n m = Fin n → Fin m

ext : Ren n m
  → Ren (suc n) (suc m)
ext ρ zero    = zero
ext ρ (suc x) = suc (ρ x)

rename     :        Ren n m → Tm n       → Tm m
renameMapᶜ : ∀ as → Ren n m → (⟦ as ⟧ᶜ Tm) n → (⟦ as ⟧ᶜ Tm) m
renameMapᵇ : ∀ a  → Ren n m → (⟦ a ⟧ᵇ  Tm) n → (⟦ a  ⟧ᵇ Tm) m

rename ρ (` x)         = ` ρ x
rename ρ (op (o , ts)) = op (o , renameMapᶜ (arity s o) ρ ts)
renameMapᶜ []       ρ _       = _
renameMapᶜ (a ∷ as) ρ (t , u) = renameMapᵇ a ρ t , renameMapᶜ as ρ u
renameMapᵇ zero     ρ t       = rename ρ t
renameMapᵇ (suc a)  ρ t       = renameMapᵇ a (ext ρ) t

infixr 5 ⟨_⟩_
⟨_⟩_ : Ren n m → Tm n → Tm m
⟨ ρ ⟩ t = rename ρ t

Sub : (n m : ℕ) → Set
Sub n m = Fin n → Tm m

exts : Sub n m → Sub (suc n) (suc m)
exts σ zero    = ` zero
exts σ (suc x) = rename suc (σ x)

subst     :        Sub n m → Tm n → Tm m
substMapᶜ : ∀ as → Sub n m → (⟦ as ⟧ᶜ Tm) n → (⟦ as ⟧ᶜ Tm) m
substMapᵇ : ∀ a  → Sub n m → (⟦ a  ⟧ᵇ Tm) n → (⟦ a  ⟧ᵇ Tm) m
subst σ (` x)         = σ x
subst σ (op (f , ts)) = op (f , substMapᶜ (arity s f) σ ts)
substMapᶜ []       σ _       = _
substMapᶜ (a ∷ as) σ (t , u) = substMapᵇ a σ t , substMapᶜ as σ u
substMapᵇ zero     σ t       = subst σ t
substMapᵇ (suc a)  σ t       = substMapᵇ a (exts σ) t

module _ {T : ℕ → Set ℓ} (α : (s -Alg) T) where mutual
  fold : Tm ⇒ T
  fold (` x)         = α .var x
  fold (op (o , as)) = α .alg (o , foldMapᶜ (arity s o) as)

  foldMapᶜ : (as : List ℕ) → ⟦ as ⟧ᶜ Tm ⇒ ⟦ as ⟧ᶜ T
  foldMapᶜ []       _       = _
  foldMapᶜ (a ∷ as) (t , u) = foldMapᵇ a t , foldMapᶜ as u

  foldMapᵇ : (a : ℕ)       → ⟦ a  ⟧ᵇ Tm ⇒ ⟦ a  ⟧ᵇ T
  foldMapᵇ zero    t = fold t
  foldMapᵇ (suc a) t = foldMapᵇ a t
