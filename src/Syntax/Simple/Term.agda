{-# OPTIONS --safe #-}

open import Prelude
open import Syntax.Simple.Description

module Syntax.Simple.Term (D : Desc) where

private variable
  Ξ Θ Θ₁ Θ₂ Θ₃ : ℕ
  n k i        : ℕ
  A B          : Set

infix 9 `_
data Tm (Θ : ℕ) : Set where
  `_ :       Fin Θ  → Tm Θ
  op : ⟦ D ⟧ (Tm Θ) → Tm Θ

Tm₀ : Set
Tm₀ = Tm 0

Tms : ℕ → Set
Tms Θ = List (Tm Θ)

module _ {X : ℕ → Set} (α : (D -Alg) X) where mutual
  fold : Tm ⇒₁ X
  fold (` x)         = α .var x
  fold (op (i , ts)) = α .alg (i , foldⁿ ts)

  foldⁿ : {l : ℕ} → Tm Θ ^ l → X Θ ^ l
  foldⁿ []       = []
  foldⁿ (t ∷ ts) = fold t ∷ foldⁿ ts

mutual
  fv : Tm Θ → List (Fin Θ)
  fv (` x)         = x ∷ []
  fv (op (i , ts)) = fvⁿ ts

  fvⁿ : Tm Θ ^ n → List (Fin Θ)
  fvⁿ []       = []
  fvⁿ (t ∷ ts) = fv t ++ fvⁿ ts
 
fvs : Tms Θ → List (Fin Θ)
fvs []       = []
fvs (t ∷ ts) = fv t ++ fvs ts

mutual
  size : Tm Θ → ℕ
  size (` x)         = 1
  size (op (_ , ts)) = suc (sizeⁿ ts)

  sizeⁿ : Tm Θ ^ n → ℕ
  sizeⁿ []       = 0
  sizeⁿ (t ∷ ts) = size t + sizeⁿ ts

mutual
  _≟ₜ_ : (t u : Tm Θ) → Dec (t ≡ u)
  (` x) ≟ₜ (` y) with  x ≟ y
  ... | yes p = yes (cong `_ p)
  ... | no ¬p = no λ where refl → ¬p refl
  op (i , ts) ≟ₜ op (j , us) with i ≟ j
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with compareMap ts us
  ... | no ¬q = no λ where refl → ¬q refl
  ... | yes q = yes (cong (λ ts → op (i , ts)) q)
  (` x) ≟ₜ op u  = no λ ()
  op x  ≟ₜ (` y) = no λ ()

  compareMap : (ts us : Tm Θ ^ n) → Dec (ts ≡ us)
  compareMap []       []        = yes refl
  compareMap (t ∷ ts) (u ∷ us) with t ≟ₜ u
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes p with compareMap ts us
  ... | no ¬q = no λ where refl → ¬q refl
  ... | yes q = yes (cong₂ _∷_ p q)

-- [TODO] Generalise it to an Any predicate
infix 4 _∈ᵥ_ _∈ᵥₛ_ _∈ᵥ?_ _∈ᵥₛ?_ _∉ᵥ_ _∉ᵥₛ_

mutual 
  data _∈ᵥ_ (x : Fin Θ) : Tm Θ → Set where
    here : {y : Fin Θ} → x ≡ y → x ∈ᵥ ` y
    op   : {i : D .Op} {ts : Tm Θ ^ D .rules i}
      → (x∈ : x ∈ᵥₛ ts) → x ∈ᵥ op (i , ts)

  data _∈ᵥₛ_ (x : Fin Θ) : Tm Θ ^ n → Set where
    head : {t : Tm Θ} {ts : Tm Θ ^ n}
      → (x∈ : x ∈ᵥ t) → x ∈ᵥₛ (t ∷ ts)
    tail : {t : Tm Θ} {ts : Tm Θ ^ n}
      → (x∈ : x ∈ᵥₛ ts) 
      → x ∈ᵥₛ (t ∷ ts)

_∉ᵥ_ : (x : Fin Θ) → Tm Θ → Set
x ∉ᵥ t = ¬ x ∈ᵥ t

_∉ᵥₛ_ : (x : Fin Θ) → Tm Θ ^ n → Set
x ∉ᵥₛ ts = ¬ x ∈ᵥₛ ts

mutual
  _∈ᵥ?_ : (x : Fin Θ) (t : Tm Θ) → Dec (x ∈ᵥ t)
  x ∈ᵥ? ` y with x ≟ y
  ... | yes p = yes (here p)
  ... | no ¬p = no λ where (here p) → ¬p p
  x ∈ᵥ? op (i , ts) with x ∈ᵥₛ? ts
  ... | yes p = yes (op p)
  ... | no ¬p = no λ where
    (op x∈) → ¬p x∈

  _∈ᵥₛ?_ : (x : Fin Θ) (ts : Tm Θ ^ n) → Dec (x ∈ᵥₛ ts)
  _∈ᵥₛ?_ {_} x [] = no λ ()
  _∈ᵥₛ?_ {_} x (t ∷ ts) with x ∈ᵥ? t
  ... | yes p = yes (head p)
  ... | no ¬p with x ∈ᵥₛ? ts
  ... | yes q = yes (tail q)
  ... | no ¬q = no λ where
    (head x∈) → ¬p x∈
    (tail x∈) → ¬q x∈

_⊆ᵥ_ : Tm Ξ → Tms Ξ → Set
A ⊆ᵥ As = ∀ {i} → i ∈ᵥ A → L.Any (i ∈ᵥ_) As

------------------------------------------------------------------------------
-- Substitution structure

Ren : ℕ → ℕ → Set
Ren Θ n = Fin Θ → Fin n -- Vec (Fin n) m

module _ (ρ : Ren Θ n) where mutual
  rename : Tm Θ → Tm n
  rename (` x)         = ` ρ x -- ` lookup ρ x
  rename (op (i , ts)) = op (i , renameⁿ ts)

  renameⁿ : {l : ℕ}
    → Tm Θ ^ l → Tm n ^ l
  renameⁿ []        = []
  renameⁿ (t ∷ ts) = rename t ∷ renameⁿ ts
  
Ren-id : Ren Θ Θ
Ren-id = λ i → i -- allFin _

Ren-⨟  : Ren Θ₁ Θ₂ → Ren Θ₂ Θ₃ → Ren Θ₁ Θ₃
Ren-⨟ σ₁ σ₂ = σ₂ ∘ σ₁ -- tabulate $ lookup σ₂ ∘ lookup σ₁

Sub : (Θ n : ℕ) → Set
Sub m n = Fin m → Tm n -- Vec (Tm n) Θ

module _ (σ : Sub Θ n) where mutual
  sub : Tm Θ → Tm n
  sub (` x)         = σ x
  sub (op (i , ts)) = op (i , subⁿ ts)

  subⁿ : {l : ℕ}
    → Tm Θ ^ l → Tm n ^ l
  subⁿ []       = []
  subⁿ (t ∷ ts) = sub t ∷ subⁿ ts

Sub-id : Sub Θ Θ
Sub-id = `_ -- tabulate `_

RenToSub : Ren Θ n → Sub Θ n
RenToSub σ = `_ ∘ σ -- tabulate (`_ ∘ σ)

Sub-⨟ : Sub Θ₁ Θ₂ → Sub Θ₂ Θ₃ → Sub Θ₁ Θ₃
Sub-⨟ σ₁ σ₂ i = sub σ₂ (σ₁ i) -- tabulate λ i → sub σ₂ (lookup σ₁ i)

------------------------------------------------------------------------------
-- Substitutio as Variable Assignment

∈Sub : Fins Ξ → ℕ → Set
∈Sub {Ξ} xs Θ = Σ ((i : Fin Ξ) → i ∈ xs → Tm Θ)
  λ ρ → ∀ {i} → (x y : i ∈ xs) → ρ i x ≡ ρ i y
  -- Liang-Ting (2023-06-08): I really want HIT to make a subset of Fin Ξ here.

∈Sub₀ : Fins Ξ → Set
∈Sub₀ xs = ∈Sub xs 0

Consistent : {xs ys : Fins Ξ}
  → (ρ : ∈Sub xs Θ) (σ : ∈Sub ys Θ) → Set
Consistent {Ξ} {_} {xs} {ys} (ρ , _) (σ , _) =
  {i : Fin _} (x : i ∈ xs) (y : i ∈ ys) → ρ i x ≡ σ i y

_⊑_ : {xs ys : Fins Ξ}
  → ∈Sub xs Θ → ∈Sub ys Θ → Set
_⊑_ {_} {_} {xs} {ys} ρ σ = xs ⊆ ys × Consistent ρ σ

module _ {vs : Fins Ξ} ((ρ , p) : ∈Sub vs Θ) where mutual
  ∈sub : (t : Tm Ξ) → fv t ⊆ vs → Tm Θ
  ∈sub (` x)         ⊆vs = ρ x (⊆vs (here refl))
  ∈sub (op (i , ts)) ⊆vs = op (i , ∈subⁿ ts ⊆vs)

  ∈subⁿ : (ts : Tm Ξ ^ n) → fvⁿ ts ⊆ vs → Tm Θ ^ n
  ∈subⁿ []       ⊆vs = []
  ∈subⁿ (t ∷ ts) ⊆vs = ∈sub t (⊆vs ∘ L.++⁺ˡ) ∷ ∈subⁿ ts (⊆vs ∘ L.++⁺ʳ _)

∅∈sub : ∈Sub {Ξ} [] Θ
∅∈sub = (λ _ ()) , λ ()
