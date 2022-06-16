open import Prelude
open import Syntax.Simple.Description

module Syntax.Simple.Term (D : Desc) where

import      Data.Fin  as F
open import Data.List as L
  using  (_++_)
open import Data.Vec  as V
  using (lookup)
open import Data.Vec.Properties as V

private variable
  Γ Ξ Δ : ℕ
  n m l : ℕ
  A B : Set

infix 9 `_
data Tm : ℕ → Set where
  `_ : Fin      ⇒₁ Tm
  op : ⟦ D ⟧ Tm ⇒₁ Tm

Tm₀ : Set
Tm₀ = Tm 0

Tms : ℕ → Set
Tms Ξ = List (Tm Ξ)

Ren : ℕ → ℕ → Set
Ren m n = Fin m → Fin n -- Vec (Fin n) m

module _ (f : Ren m n) where mutual
  rename : Tm m → Tm n
  rename (` x)             = ` f x
  rename (op (_ , i , ts)) = op (_ , i , renameⁿ ts)

  renameⁿ : {l : ℕ}
    → Tm m ^ l → Tm n ^ l
  renameⁿ {l = zero}  _        = _
  renameⁿ {l = suc n} (t , ts) = rename t , renameⁿ ts

Sub : (m n : ℕ) → Set
Sub m n = Vec (Tm n) m

Sub₀ : (Ξ : ℕ) → Set
Sub₀ Ξ = Sub Ξ 0

module _ (σ : Sub m n) where mutual
  sub : Tm m → Tm n
  sub (` x)  = lookup σ x
  sub (op (_ , i , ts)) = op (_ , i , subⁿ _ ts)

  subⁿ : ∀ l
    → Tm m ^ l → Tm n ^ l
  subⁿ zero    _        = _
  subⁿ (suc n) (t , ts) = sub t , subⁿ n ts

infixr 8 ⟨_⟩_ ⟪_⟫_

⟨_⟩_ : Ren m n → Tm m → Tm n
⟨ f ⟩ t = rename f t

idr : Ren m m
idr = id

weaken : Tm m → Tm (suc m)
weaken = rename suc

⟪_⟫_ : Sub m n → Tm m → Tm n
⟪ f ⟫ t = sub f t

ids : Sub m m
ids {m = zero}  = []
ids {m = suc m} = ` zero ∷ V.map weaken ids

ids-at-x=x : (x : Fin n)
  → V.lookup ids x ≡ ` x
ids-at-x=x {n = suc n} zero    = refl
ids-at-x=x {n = suc n} (suc x) = begin
  lookup (V.map weaken ids) x
    ≡⟨ lookup-map x weaken ids ⟩
  weaken (lookup ids x)
    ≡⟨ cong weaken (ids-at-x=x x) ⟩
  weaken (` x)
    ≡⟨⟩
  ` suc x
    ∎
  where open ≡-Reasoning

mutual
  sub-id : (t : Tm m)
    → ⟪ ids ⟫ t ≡ t
  sub-id {m = zero} (op (_ , i , ts)) =
    cong (λ ts → op (_ , i , ts)) (sub-idⁿ ts)
  sub-id {m = suc m} (` x)  = ids-at-x=x x
  sub-id {m = suc m} (op (_ , i , ts)) =
    cong (λ ts → op (_ , i , ts)) (sub-idⁿ ts)

  sub-idⁿ : (t : Tm m ^ l)
    → subⁿ ids l t ≡ t
  sub-idⁿ {l = zero}  t        = refl
  sub-idⁿ {l = suc l} (t , ts) =
    cong₂ _,_ (sub-id t) (sub-idⁿ ts)

_◇_ : Sub m n → Sub n l → Sub m l
σ₁ ◇ σ₂ = V.map (sub σ₂) σ₁

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
  fvⁿ {n = suc n} (t , ts) = fv t ++ fvⁿ ts

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

_≟s_ : (σ σ′ : Sub Ξ Δ) → Dec (σ ≡ σ′)
[]      ≟s []      = yes refl
(A ∷ Δ) ≟s (B ∷ Γ) with A ≟ B
... | no ¬p =  no λ where refl → ¬p refl
... | yes p with Δ ≟s Γ 
... | no ¬q =  no λ where refl → ¬q refl
... | yes q =  yes (cong₂ _∷_ p q)