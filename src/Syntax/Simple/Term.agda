{-# OPTIONS --with-K --safe #-}

open import Prelude
open import Syntax.Simple.Description

module Syntax.Simple.Term (D : Desc) where

import Data.Fin            as F
import Data.Vec            as V
import Data.Vec.Properties as V

private variable
  Γ Ξ Δ : ℕ
  n m l k : ℕ
  A B : Set

infix 9 `_
data Tm (n : ℕ) : Set where
  `_ :       Fin n  → Tm n -- Fin        ⇒₁ Tm
  op : ⟦ D ⟧ (Tm n) → Tm n -- ⟦ D ⟧ ∘ Tm ⇒₁ Tm

Tm₀ : Set
Tm₀ = Tm 0

Tms : ℕ → Set
Tms Ξ = List (Tm Ξ)

Ren : ℕ → ℕ → Set
Ren m n = Vec (Fin n) m -- Fin m → Fin n

module _ (ρ : Ren m n) where mutual
  rename : Tm m → Tm n
  rename (` x)             = ` V.lookup ρ x
  rename (op (_ , i , ts)) = op (_ , i , renameⁿ ts)

  renameⁿ : {l : ℕ}
    → Tm m ^ l → Tm n ^ l
  renameⁿ {l = zero}  _        = _
  renameⁿ {l = suc n} (t , ts) = rename t , renameⁿ ts

injectˡ : Ren m (m + n)
injectˡ = V.tabulate λ i → F._↑ˡ_ i _ -- λ i → F._↑ˡ_ i _

insert-mid : (m n : ℕ) → Fin (m + l) → Fin (m + n + l)
insert-mid m n i with F.splitAt m i
... | inl j = (j F.↑ˡ _) F.↑ˡ _
... | inr k = (m + n) F.↑ʳ k

wkʳ : Tm m → Tm (n + m)
wkʳ = rename (V.tabulate (F._↑ʳ_ _)) -- (F._↑ʳ_ _)

wkˡ : Tm m → Tm (m + n)
wkˡ = rename injectˡ

wkᵐ : (m n : ℕ) → Tm (m + l) → Tm (m + n + l)
wkᵐ m n = rename (V.tabulate (insert-mid m n)) -- (insert-mid m n)

wk≤ˡ : m ≤ n → Tm m → Tm n
wk≤ˡ (less-than-or-equal refl) = wkˡ

weaken : Tm m → Tm (suc m)
weaken = rename (V.tabulate suc)

infixl 8 _⟨_⟩ _⟪_⟫

_⟨_⟩ : Tm m → Ren m n → Tm n
t ⟨ f ⟩ = rename f t

idr : Ren m m
idr = V.allFin _

Sub : (m n : ℕ) → Set
Sub m n = Vec (Tm n) m

module _ (σ : Sub m n) where mutual
  sub : Tm m → Tm n
  sub (` x)  = V.lookup σ x
  sub (op (_ , i , ts)) = op (_ , i , subⁿ ts)

  subⁿ : {l : ℕ}
    → Tm m ^ l → Tm n ^ l
  subⁿ {zero}  _        = _
  subⁿ {suc n} (t , ts) = sub t , subⁿ ts

_⟪_⟫ : Tm m → Sub m n → Tm n
t ⟪ f ⟫ = sub f t

{-# DISPLAY sub σ t = t ⟪ σ ⟫ #-}

ids : Sub m m
ids = V.tabulate `_ -- `_

_⨟_ : Sub m n → Sub n l → Sub m l
(σ₁ ⨟ σ₂) = V.tabulate λ i →  (V.lookup σ₁ i)⟪ σ₂ ⟫

∅ₛ : Sub 0 n
∅ₛ = []

_∙ₛ_ : Tm n → Sub m n → Sub (suc m) n
(t ∙ₛ σ) = t ∷ σ
-- (t ∙ₛ σ)  zero   = t
-- (t ∙ₛ σ) (suc i) = σ i

infixr 5 _∙ₛ_

module _ {m : ℕ} where mutual
  sub-id : (t : Tm m)
    → t ⟪ ids ⟫ ≡ t
  sub-id (` x)             = V.lookup∘tabulate `_ x
  sub-id (op (_ , i , ts)) = cong (λ ts → op (_ , i , ts)) (sub-idⁿ ts)

  sub-idⁿ : (t : Tm m ^ l)
    → subⁿ ids t ≡ t
  sub-idⁿ {zero}  t        = refl
  sub-idⁿ {suc l} (t , ts) =
    cong₂ _,_ (sub-id t) (sub-idⁿ ts)

module _ {m n l : ℕ} (ρ : Sub m n) (σ : Sub n l) where mutual
  sub-assoc : (t : Tm m)
    → t ⟪ ρ ⨟ σ ⟫ ≡ t ⟪ ρ ⟫ ⟪ σ ⟫
  sub-assoc (` x)             = V.lookup∘tabulate (λ i → V.lookup ρ i ⟪ σ ⟫) x
  sub-assoc (op (k , i , ts)) = cong (λ ts → op (_ , i , ts)) (sub-assocⁿ ts)

  sub-assocⁿ : (ts : Tm m ^ k)
    → subⁿ (ρ ⨟ σ) ts ≡ subⁿ σ (subⁿ ρ ts) 
  sub-assocⁿ {zero}  ts       = refl
  sub-assocⁿ {suc k} (t , ts) = cong₂ _,_ (sub-assoc t) (sub-assocⁿ ts)


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
... | no ¬p = ` F.punchOut ¬p
... | yes _ = t

_for_
  : Tm m → Fin (suc m)
  → Sub (suc m) m
(t for x) = V.tabulate (sub-for t x)

sub-t-for-x-x
  : {t : Tm m} {x : Fin (suc m)}
  → sub-for t x x ≡ t
sub-t-for-x-x {x = x} with x F.≟ x
... | yes p = refl
... | no ¬p = ⊥-elim₀ (¬p refl)

sub-t-for-x-y
  : {x y : Fin (suc m)} {t : Tm m} 
  → (¬p : x ≢ y)
  → sub-for t x y ≡ ` F.punchOut ¬p 
sub-t-for-x-y {x = x} {y} ¬p with x F.≟ y
... | yes p = ⊥-elim₀ (¬p p)
... | no ¬p = refl

sub-for-x-in-x : {t : Tm m} (x : Fin (suc m))
  → ` x ⟪ t for x ⟫ ≡ t
sub-for-x-in-x {t = t} x = begin
  ` x ⟪ t for x ⟫
    ≡⟨ V.lookup∘tabulate (sub-for t x) x ⟩
  sub-for t x x
    ≡⟨ sub-t-for-x-x ⟩
  t
    ∎
  where open ≡-Reasoning

sub-for-x-in-y : {t : Tm m} {x y : Fin (suc m)}
  → (¬p : x ≢ y)
  → ` y ⟪ t for x ⟫ ≡ ` F.punchOut ¬p
sub-for-x-in-y {m} {t} {x} {y} ¬p = begin
  ` y ⟪ t for x ⟫
    ≡⟨ V.lookup∘tabulate (sub-for t x) y ⟩
  sub-for t x y
    ≡⟨ sub-t-for-x-y ¬p ⟩
  ` F.punchOut ¬p
    ∎
  where open ≡-Reasoning

-- Utilities for checking free variables

open import Data.List.Membership.Propositional.Properties
mutual
  checkFv : (x : Fin m) (t : Tm m) → Dec (x ∈ fv t)
  checkFv x (` y)  with x F.≟ y
  ... | yes p = yes (here p)
  ... | no ¬p = no λ where (here p) → ¬p p
  checkFv x (op (_ , _ , ts)) = checkFvⁿ x ts

  checkFvⁿ : (x : Fin m) (t : Tm m ^ l) → Dec (x ∈ fvⁿ t)
  checkFvⁿ {l = zero}  _ _        = no λ ()
  checkFvⁿ {l = suc l} x (t , ts) with checkFv x t
  ... | yes p = yes (∈-++⁺ˡ p)
  ... | no ¬p with checkFvⁿ x ts
  ... | yes q = yes (∈-++⁺ʳ (fv t) q)
  ... | no ¬q = no λ where x → case ∈-++⁻ (fv t) x of λ where
    (inl ∈t)  → ¬p ∈t
    (inr ∈ts) → ¬q ∈ts

mutual
  punchOutTm : (x : Fin (suc Ξ)) (t : Tm (suc Ξ))
    → ¬ x ∈ fv t → Tm Ξ
  punchOutTm x (` y)  x∉ with x F.≟ y
  ... | yes x=y = ⊥-elim₀ (x∉ (here x=y))
  ... | no ¬x=y = ` F.punchOut ¬x=y
  punchOutTm x (op (_ , i , ts)) x∉ =
    op (_ , i , punchOutTmⁿ x ts x∉)

  punchOutTmⁿ : (x : Fin (suc Ξ)) (ts : Tm (suc Ξ) ^ n)
    → ¬ x ∈ fvⁿ ts → Tm Ξ ^ n
  punchOutTmⁿ {n = zero}  _ _        _    = _ 
  punchOutTmⁿ {n = suc l} x (t , ts) x∉ =
    punchOutTm x t (x∉ ∘ ∈-++⁺ˡ) , punchOutTmⁿ x ts (x∉ ∘ ∈-++⁺ʳ (fv t))

module _ {u : Tm m} {x : Fin (suc m)} where mutual
  sub-for-nonfree=punchOut : (t : Tm (suc m)) (x∉ : ¬ x ∈ fv t)
    → t ⟪ u for x ⟫ ≡ punchOutTm x t x∉
  sub-for-nonfree=punchOut (` y)  x∉ with x F.≟ y
  ... | yes p = ⊥-elim₀ (x∉ (here p))
  ... | no ¬p = sub-for-x-in-y ¬p
  sub-for-nonfree=punchOut (op (_ , i , ts)) x∉ =
    cong (λ ts → op (_ , i , ts)) (sub-for-nonfree=punchOutⁿ ts x∉)

  sub-for-nonfree=punchOutⁿ : (ts : Tm (suc m) ^ n)
    → (x∉ : ¬ x ∈ fvⁿ ts)
    → subⁿ (u for x) ts ≡ punchOutTmⁿ x ts x∉
  sub-for-nonfree=punchOutⁿ {n = zero}  _        _  = refl
  sub-for-nonfree=punchOutⁿ {n = suc n} (t , ts) x∉ =
    cong₂ _,_ (sub-for-nonfree=punchOut t $ x∉ ∘ ∈-++⁺ˡ)
      (sub-for-nonfree=punchOutⁿ ts (x∉ ∘ ∈-++⁺ʳ (fv t)))
