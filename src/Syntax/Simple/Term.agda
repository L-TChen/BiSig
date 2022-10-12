open import Prelude
open import Syntax.Simple.Description

module Syntax.Simple.Term (D : Desc) where

import      Data.Fin  as F

open import Syntax.Context
  using (Context)

private variable
  Γ Ξ Δ : ℕ
  n m l : ℕ
  A B : Set

infix 9 `_
data Tm : ℕ → Set where
  `_ : Fin      ⇒₁ Tm
  op : ⟦ D ⟧ Tm ⇒₁ Tm

Cxt : ℕ → Set
Cxt m = Context (Tm m)

Tm₀ : Set
Tm₀ = Tm 0

Tms : ℕ → Set
Tms Ξ = List (Tm Ξ)

Ren : ℕ → ℕ → Set
Ren m n = Fin m → Fin n

module _ (f : Ren m n) where mutual
  rename : Tm m → Tm n
  rename (` x)             = ` f x
  rename (op (_ , i , ts)) = op (_ , i , renameⁿ ts)

  renameⁿ : {l : ℕ}
    → Tm m ^ l → Tm n ^ l
  renameⁿ {l = zero}  _        = _
  renameⁿ {l = suc n} (t , ts) = rename t , renameⁿ ts

wkʳ : Tm m → Tm (n + m)
wkʳ = rename (F._↑ʳ_ _) 

wkˡ : Tm m → Tm (m + n)
wkˡ = rename λ i → F._↑ˡ_ i _

insert-mid : (m n : ℕ) → Fin (m + l) → Fin (m + n + l)
insert-mid m n i with F.splitAt m i
... | inl j = (j F.↑ˡ _) F.↑ˡ _ 
... | inr k = (m + n) F.↑ʳ k

wkᵐ : (m n : ℕ) → Tm (m + l) → Tm (m + n + l)
wkᵐ m n = rename (insert-mid m n)

wk≤ˡ : m ≤ n → Tm m → Tm n
wk≤ˡ (less-than-or-equal refl) = wkˡ 

weaken : Tm m → Tm (suc m)
weaken = rename suc

⟨_⟩_ : Ren m n → Tm m → Tm n
⟨ f ⟩ t = rename f t

idr : Ren m m
idr = id

Sub : (m n : ℕ) → Set
Sub m n = Fin m → Tm n

module _ (σ : Sub m n) where mutual
  sub : Tm m → Tm n
  sub (` x)  = σ x
  sub (op (_ , i , ts)) = op (_ , i , subⁿ _ ts)

  subⁿ : ∀ l
    → Tm m ^ l → Tm n ^ l
  subⁿ zero    _        = _
  subⁿ (suc n) (t , ts) = sub t , subⁿ n ts

infixr 8 ⟨_⟩_ ⟪_⟫_

⟪_⟫_ : Sub m n → Tm m → Tm n
⟪ f ⟫ t = sub f t

ids : Sub m m
ids = `_

_⨟_ : Sub m n → Sub n l → Sub m l
(σ₁ ⨟ σ₂) i = ⟪ σ₂ ⟫ σ₁ i

mutual
  sub-id : (t : Tm m)
    → ⟪ ids ⟫ t ≡ t
  sub-id {m = zero} (op (_ , i , ts)) =
    cong (λ ts → op (_ , i , ts)) (sub-idⁿ ts)
  sub-id {m = suc m} (` x)  = refl -- ids-at-x=x x
  sub-id {m = suc m} (op (_ , i , ts)) =
    cong (λ ts → op (_ , i , ts)) (sub-idⁿ ts)

  sub-idⁿ : (t : Tm m ^ l)
    → subⁿ ids l t ≡ t
  sub-idⁿ {l = zero}  t        = refl
  sub-idⁿ {l = suc l} (t , ts) =
    cong₂ _,_ (sub-id t) (sub-idⁿ ts)

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

thick : (x y : Fin (suc m)) → Maybe (Fin m)
thick {m = zero}  zero zero       = nothing
thick {m = suc m} zero zero       = nothing
thick {m = suc m} zero (suc y)    = just y
thick {m = suc m} (suc x) zero    = just zero
thick {m = suc m} (suc x) (suc y) with thick x y
... | just y′ = just (suc y′)
... | nothing = nothing

_for_
  : Tm Ξ → Fin (suc Ξ)
  → Sub (suc Ξ) Ξ
(t for x) y with thick x y
... | just y′ = ` y′
... | nothing = t
