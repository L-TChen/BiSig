{-# OPTIONS --with-K --safe #-}

open import Prelude
open import Syntax.Simple.Description

module Syntax.Simple.Term (D : Desc) where

open import Data.Fin            as F
  using (_↑ˡ_; _↑ʳ_; punchOut; splitAt)
open import Data.Vec            as V
  using (lookup; tabulate; allFin)

private variable
  Γ Ξ Δ : ℕ
  n m l k : ℕ
  A B : Set

infix 9 `_
data Tm (n : ℕ) : Set where
  `_ :       Fin n  → Tm n
  op : ⟦ D ⟧ (Tm n) → Tm n

Tm₀ : Set
Tm₀ = Tm 0

Tms : ℕ → Set
Tms Ξ = List (Tm Ξ)

Ren : ℕ → ℕ → Set
Ren m n = Vec (Fin n) m -- Fin m → Fin n

module _ (ρ : Ren m n) where mutual
  rename : Tm m → Tm n
  rename (` x)             = ` lookup ρ x
  rename (op (_ , i , ts)) = op (_ , i , renameⁿ ts)

  renameⁿ : {l : ℕ}
    → Tm m ^ l → Tm n ^ l
  renameⁿ {l = zero}  _        = _
  renameⁿ {l = suc n} (t , ts) = rename t , renameⁿ ts

injectˡ : Ren m (m + n)
injectˡ = tabulate λ i → _↑ˡ_ i _ -- λ i → F._↑ˡ_ i _

insert-mid : (m n : ℕ) → Fin (m + l) → Fin (m + n + l)
insert-mid m n i with splitAt m i
... | inl j = (j ↑ˡ _) ↑ˡ _
... | inr k = (m + n) ↑ʳ k

wkʳ : Tm m → Tm (n + m)
wkʳ = rename (tabulate (_↑ʳ_ _)) -- (F._↑ʳ_ _)

wkˡ : Tm m → Tm (m + n)
wkˡ = rename injectˡ

wkᵐ : (m n : ℕ) → Tm (m + l) → Tm (m + n + l)
wkᵐ m n = rename (tabulate (insert-mid m n)) -- (insert-mid m n)

wk≤ˡ : m ≤ n → Tm m → Tm n
wk≤ˡ (less-than-or-equal refl) = wkˡ

weaken : Tm m → Tm (suc m)
weaken = rename (tabulate suc)

infixl 8 _⟨_⟩ _⟪_⟫

_⟨_⟩ : Tm m → Ren m n → Tm n
t ⟨ f ⟩ = rename f t

idr : Ren m m
idr = allFin _

Sub : (m n : ℕ) → Set
Sub m n = Vec (Tm n) m

module _ (σ : Sub m n) where mutual
  sub : Tm m → Tm n
  sub (` x)  = lookup σ x
  sub (op (_ , i , ts)) = op (_ , i , subⁿ ts)

  subⁿ : {l : ℕ}
    → Tm m ^ l → Tm n ^ l
  subⁿ {zero}  _        = _
  subⁿ {suc n} (t , ts) = sub t , subⁿ ts

_⟪_⟫ : Tm m → Sub m n → Tm n
t ⟪ f ⟫ = sub f t

{-# DISPLAY sub σ t = t ⟪ σ ⟫ #-}

ids : Sub m m
ids = tabulate `_

_⨟_ : Sub m n → Sub n l → Sub m l
(σ₁ ⨟ σ₂) = tabulate λ i →  (lookup σ₁ i)⟪ σ₂ ⟫

_⊑_ : Sub m n → Sub m l → Set
ρ ⊑ σ = ∃[ ρ′ ] ρ ≡ (σ ⨟ ρ′) 

∅ₛ : Sub 0 n
∅ₛ = []

_∙ₛ_ : Tm n → Sub m n → Sub (suc m) n
(t ∙ₛ σ) = t ∷ σ

infixr 5 _∙ₛ_

module _ {X : ℕ → Set} (α : (D -Alg) X) where mutual
  fold : Tm ⇒₁ X
  fold (` x)  = α .var x
  fold (op (_ , i , ts)) = α .alg (_ , i , foldⁿ ts)

  foldⁿ : {l : ℕ} → Tm m ^ l → X m ^ l
  foldⁿ {l = zero  }  _        = _
  foldⁿ {l = suc n } (t , ts) = fold t , foldⁿ ts

mutual
  fv : Tm Ξ → List (Fin Ξ)
  fv (` x)  = x ∙ ∅
  fv (op (n , i , ts)) = fvⁿ ts

  fvⁿ : Tm Ξ ^ n → List (Fin Ξ)
  fvⁿ {n = zero}  _        = ∅
  fvⁿ {n = suc n} (t , ts) = fv t ++ fvⁿ ts -- fv t ++ fvⁿ ts

mutual
  _≟_ : (t u : Tm Ξ) → Dec (t ≡ u)
  (` x) ≟ (` y) with  x F.≟ y
  ... | yes p = yes (cong `_ p)
  ... | no ¬p = no λ where refl → ¬p refl
  op (D , i , ts) ≟ op (_ , j , us) with i ≟∈ j
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with compareMap ts us
  ... | no ¬q = no λ where refl → ¬q refl
  ... | yes q = yes (cong (λ ts → op (D , i , ts)) q)
  (` x) ≟ op u  = no λ ()
  op x  ≟ (` y) = no λ ()

  compareMap : (ts us : Tm Ξ ^ n) → Dec (ts ≡ us)
  compareMap {n = zero}  _        _        = yes refl
  compareMap {n = suc n} (t , ts) (u , us) with t ≟ u
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes p with compareMap ts us
  ... | no ¬q = no λ where refl → ¬q refl
  ... | yes q = yes (cong₂ _,_ p q)

sub-for : (Tm m) → (x y : Fin (suc m)) → Tm m
sub-for t x y with x F.≟ y
... | no ¬p = ` punchOut ¬p
... | yes _ = t

_for_
  : Tm m → Fin (suc m)
  → Sub (suc m) m
(t for x) = tabulate (sub-for t x)

-- Utilities for checking free variables

infix 4 _∈ₜ_ _∈ₜₛ_ _∈ₜ?_ _∈ₜₛ?_ _∉ₜ_ _∉ₜₛ_

mutual 
  data _∈ₜ_ (x : Fin m) : Tm m → Set where
    here : {y : Fin m} → x ≡ y → x ∈ₜ ` y
    ops  : {n : ℕ} {i : n ∈ D} {ts : Tm m ^ n}
      → (x∈ : x ∈ₜₛ ts) → x ∈ₜ op (n , i , ts)

  data _∈ₜₛ_ (x : Fin m) : Tm m ^ n → Set where
    head : {t : Tm m} {ts : Tm m ^ n}
      → (x∈ : x ∈ₜ t) → x ∈ₜₛ (t , ts)
    tail : {t : Tm m} {ts : Tm m ^ n}
      → (x∈ : x ∈ₜₛ ts) 
      → x ∈ₜₛ (t , ts)

_∉ₜ_ : (x : Fin m) → Tm m → Set
x ∉ₜ t = ¬ x ∈ₜ t

_∉ₜₛ_ : (x : Fin m) → Tm m ^ n → Set
x ∉ₜₛ ts = ¬ x ∈ₜₛ ts

mutual
  _∈ₜ?_ : (x : Fin m) (t : Tm m) → Dec (x ∈ₜ t)
  x ∈ₜ? ` y with x F.≟ y
  ... | yes p = yes (here p)
  ... | no ¬p = no λ where (here p) → ¬p p
  x ∈ₜ? op (_ , _ , ts) with x ∈ₜₛ? ts
  ... | yes p = yes (ops p)
  ... | no ¬p = no λ where
    (ops x∈) → ¬p x∈

  _∈ₜₛ?_ : (x : Fin m) (ts : Tm m ^ l) → Dec (x ∈ₜₛ ts)
  _∈ₜₛ?_ {_} {zero}  x tt = no λ ()
  _∈ₜₛ?_ {_} {suc l} x (t , ts) with x ∈ₜ? t
  ... | yes p = yes (head p)
  ... | no ¬p with x ∈ₜₛ? ts
  ... | yes q = yes (tail q)
  ... | no ¬q = no λ where
    (head x∈) → ¬p x∈
    (tail x∈) → ¬q x∈

mutual
  punchOutTm : (x : Fin (suc Ξ)) (t : Tm (suc Ξ))
    → ¬ x ∈ₜ t → Tm Ξ
  punchOutTm x (` y)  x∉ with x F.≟ y
  ... | yes x=y = ⊥-elim₀ (x∉ (here x=y))
  ... | no ¬x=y = ` punchOut ¬x=y
  punchOutTm x (op (_ , i , ts)) x∉ =
    op (_ , i , punchOutTmⁿ x ts (x∉ ∘ ops))

  punchOutTmⁿ : (x : Fin (suc Ξ)) (ts : Tm (suc Ξ) ^ n)
    → ¬ x ∈ₜₛ ts → Tm Ξ ^ n
  punchOutTmⁿ {n = zero}  _ _        _    = _ 
  punchOutTmⁿ {n = suc l} x (t , ts) x∉ = punchOutTm x t (x∉ ∘ head) , punchOutTmⁿ x ts (x∉ ∘ tail)
