{-# OPTIONS --with-K --safe #-}

open import Prelude
open import Syntax.Simple.Description

module Syntax.Simple.Term (D : Desc) where

import Relation.Binary.Construct.On as On

private variable
  Γ Ξ Δ : ℕ
  n m l k i j : ℕ
  A B : Set

infix 9 `_
data Tm (n : ℕ) : Set where
  `_ :       Fin n  → Tm n
  op : ⟦ D ⟧ (Tm n) → Tm n

pattern op′ i ts = op (_ , i , ts)

Tm₀ : Set
Tm₀ = Tm 0

Tms : ℕ → Set
Tms Ξ = List (Tm Ξ)

module _ {X : ℕ → Set} (α : (D -Alg) X) where mutual
  fold : Tm ⇒₁ X
  fold (` x)             = α .var x
  fold (op (_ , i , ts)) = α .alg (_ , i , foldⁿ ts)

  foldⁿ : {l : ℕ} → Tm m ^ l → X m ^ l
  foldⁿ []       = []
  foldⁿ (t ∷ ts) = fold t ∷ foldⁿ ts

mutual
  fv : Tm Ξ → List (Fin Ξ)
  fv (` x)             = x ∷ []
  fv (op (n , i , ts)) = fvⁿ ts

  fvⁿ : Tm Ξ ^ n → List (Fin Ξ)
  fvⁿ []       = []
  fvⁿ (t ∷ ts) = fv t ++ fvⁿ ts
  
mutual
  size : Tm m → ℕ
  size (` x)      = 1
  size (op′ _ ts) = suc (sizeⁿ ts)

  sizeⁿ : Tm m ^ l → ℕ
  sizeⁿ []       = 0
  sizeⁿ (t ∷ ts) = size t + sizeⁿ ts
  
mutual
  _≟ₜ_ : (t u : Tm Ξ) → Dec (t ≡ u)
  (` x) ≟ₜ (` y) with  x ≟ y
  ... | yes p = yes (cong `_ p)
  ... | no ¬p = no λ where refl → ¬p refl
  op (D , i , ts) ≟ₜ op (_ , j , us) with i ≟∈ j
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with compareMap ts us
  ... | no ¬q = no λ where refl → ¬q refl
  ... | yes q = yes (cong (λ ts → op (D , i , ts)) q)
  (` x) ≟ₜ op u  = no λ ()
  op x  ≟ₜ (` y) = no λ ()

  compareMap : (ts us : Tm Ξ ^ n) → Dec (ts ≡ us)
  compareMap []       []        = yes refl
  compareMap (t ∷ ts) (u ∷ us) with t ≟ₜ u
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes p with compareMap ts us
  ... | no ¬q = no λ where refl → ¬q refl
  ... | yes q = yes (cong₂ _∷_ p q)

infix 4 _∈ₜ_ _∈ₜₛ_ _∈ₜ?_ _∈ₜₛ?_ _∉ₜ_ _∉ₜₛ_

mutual 
  data _∈ₜ_ (x : Fin m) : Tm m → Set where
    here : {y : Fin m} → x ≡ y → x ∈ₜ ` y
    ops  : {n : ℕ} {i : n ∈ D} {ts : Tm m ^ n}
      → (x∈ : x ∈ₜₛ ts) → x ∈ₜ op (n , i , ts)

  data _∈ₜₛ_ (x : Fin m) : Tm m ^ n → Set where
    head : {t : Tm m} {ts : Tm m ^ n}
      → (x∈ : x ∈ₜ t) → x ∈ₜₛ (t ∷ ts)
    tail : {t : Tm m} {ts : Tm m ^ n}
      → (x∈ : x ∈ₜₛ ts) 
      → x ∈ₜₛ (t ∷ ts)

_∉ₜ_ : (x : Fin m) → Tm m → Set
x ∉ₜ t = ¬ x ∈ₜ t

_∉ₜₛ_ : (x : Fin m) → Tm m ^ n → Set
x ∉ₜₛ ts = ¬ x ∈ₜₛ ts

mutual
  _∈ₜ?_ : (x : Fin m) (t : Tm m) → Dec (x ∈ₜ t)
  x ∈ₜ? ` y with x ≟ y
  ... | yes p = yes (here p)
  ... | no ¬p = no λ where (here p) → ¬p p
  x ∈ₜ? op (_ , _ , ts) with x ∈ₜₛ? ts
  ... | yes p = yes (ops p)
  ... | no ¬p = no λ where
    (ops x∈) → ¬p x∈

  _∈ₜₛ?_ : (x : Fin m) (ts : Tm m ^ l) → Dec (x ∈ₜₛ ts)
  _∈ₜₛ?_ {_} x [] = no λ ()
  _∈ₜₛ?_ {_} x (t ∷ ts) with x ∈ₜ? t
  ... | yes p = yes (head p)
  ... | no ¬p with x ∈ₜₛ? ts
  ... | yes q = yes (tail q)
  ... | no ¬q = no λ where
    (head x∈) → ¬p x∈
    (tail x∈) → ¬q x∈

length∈ₜₛ : {x : Fin m} {ts : Tm m ^ l} → x ∈ₜₛ ts → Fin l
length∈ₜₛ (head x∈) = zero
length∈ₜₛ (tail x∈) = suc (length∈ₜₛ x∈)

lookup∈ₜₛ : {x : Fin m} {ts : Tm m ^ l}
  → (i : x ∈ₜₛ ts)
  → x ∈ₜ lookup ts (length∈ₜₛ i) 
lookup∈ₜₛ (head x∈) = x∈
lookup∈ₜₛ (tail x∈) = lookup∈ₜₛ x∈

mutual
  punchOutTm : {x : Fin (suc n)} {t : Tm (suc n)}
    → ¬ x ∈ₜ t → Tm n
  punchOutTm {_} {x} {` y}  x∉ with x ≟ y
  ... | yes x=y = ⊥-elim₀ (x∉ (here x=y))
  ... | no ¬x=y = ` punchOut ¬x=y
  punchOutTm {_} {x} {op (_ , i , ts)} x∉ =
    op (_ , i , punchOutTmⁿ (x∉ ∘ ops))

  punchOutTmⁿ : {x : Fin (suc Ξ)} {ts : Tm (suc Ξ) ^ n}
    → ¬ x ∈ₜₛ ts → Tm Ξ ^ n
  punchOutTmⁿ {ts = []}     _  = []
  punchOutTmⁿ {ts = t ∷ ts} x∉ =
    punchOutTm (x∉ ∘ head) ∷ punchOutTmⁿ (x∉ ∘ tail)

Ren : ℕ → ℕ → Set
Ren m n = Vec (Fin n) m

module _ (ρ : Ren m n) where mutual
  rename : Tm m → Tm n
  rename (` x)             = ` lookup ρ x
  rename (op (_ , i , ts)) = op (_ , i , renameⁿ ts)

  renameⁿ : {l : ℕ}
    → Tm m ^ l → Tm n ^ l
  renameⁿ []        = []
  renameⁿ (t ∷ ts) = rename t ∷ renameⁿ ts

Sub : (m n : ℕ) → Set
Sub m n = Vec (Tm n) m

module _ (σ : Sub m n) where mutual
  sub : Tm m → Tm n
  sub (` x)  = lookup σ x
  sub (op (_ , i , ts)) = op (_ , i , subⁿ ts)

  subⁿ : {l : ℕ}
    → Tm m ^ l → Tm n ^ l
  subⁿ []       = []
  subⁿ (t ∷ ts) = sub t ∷ subⁿ ts

infixl 8 _⟨_⟩ _⟪_⟫

_⟨_⟩ : Tm m → Ren m n → Tm n
t ⟨ f ⟩ = rename f t

_⟪_⟫ : Tm m → Sub m n → Tm n
t ⟪ f ⟫ = sub f t

{-# DISPLAY sub σ t = t ⟪ σ ⟫ #-}

idr : Ren m m
idr = allFin _

ids : Sub m m
ids = tabulate `_

_⨟_ : Sub m n → Sub n l → Sub m l
(σ₁ ⨟ σ₂) = tabulate λ i →  (lookup σ₁ i)⟪ σ₂ ⟫

∅ₛ : Sub 0 n
∅ₛ = []

_∙ₛ_ : Tm n → Sub m n → Sub (suc m) n
(t ∙ₛ σ) = t ∷ σ

infixr 5 _∙ₛ_

sub-for : (Tm m) → (x y : Fin (suc m)) → Tm m
sub-for t x y with x ≟ y
... | no ¬p = ` punchOut ¬p
... | yes _ = t

_for_
  : Tm m → Fin (suc m)
  → Sub (suc m) m
t for x = tabulate (sub-for t x)

injectˡ : Ren m (m + n)
injectˡ = tabulate λ i → _↑ˡ_ i _ -- λ i → F._↑ˡ_ i _

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

------------------------------------------------------------------------------
-- Order relation between substitutions

private variable
  t u v : Tm m

_⊑_ : Sub m n → Sub m l → Set
ρ ⊑ σ = ∃[ ρ′ ] ρ ≡ (σ ⨟ ρ′) 

Subₚ = λ m → {n : ℕ} → Sub m n → Set

Unifies : (t u : Tm m) → Subₚ m
Unifies t u σ = t ⟪ σ ⟫ ≡ u ⟪ σ ⟫ 

infixl 10 _[_⨟_]
_[_⨟_] : (P : Subₚ m) (σ : Sub m n) → Subₚ n
P [ σ ⨟ ρ ] = P (σ ⨟ ρ)

{-
lem : (P : Subₚ m) (σ₁ : Sub m n) (σ₂ : Sub n l) (ρ : Sub l k)
  → P [ σ₁ ⨟_] [ σ₂ ⨟ ρ ] → P [ (σ₁ ⨟ σ₂) ⨟ ρ ]
lem P σ₁ σ₂ ρ k = {!!}
-}

Max : Subₚ m → Subₚ m
Max P σ = P σ ×
  ({n : ℕ} (σ′ : Sub _ n) → P σ′ → σ′ ⊑  σ)

------------------------------------------------------------------------------
-- Zipper for Simple Terms

record Step (n : ℕ) : Set where
  constructor step
  field
    {iᵤ iₜ} : ℕ 
    pos : iᵤ ʳ+ suc iₜ ∈ D
    us  : Tm n ^ iᵤ
    ts  : Tm n ^ iₜ
open Step public using ()

Steps : ℕ → Set
Steps n = List (Step n)

_⟪_⟫′ : Steps m → Sub m n → Steps n
[]       ⟪ σ ⟫′ = []
(step pos us ts ∷ ps) ⟪ σ ⟫′ =
  step pos (subⁿ σ us) (subⁿ σ ts) ∷ ps ⟪ σ ⟫′

infixr 4.5 _▷₁_ _▷_

_▷₁_ : Step n → Tm n → Tm n
step i us ts ▷₁ t = op′ i $ us ʳ++ (t ∷ ts)

_▷_ : Steps n → Tm n → Tm n
[]       ▷ t = t
(p ∷ ps) ▷ t = p ▷₁ (ps ▷ t)

module _ {m : ℕ} {x : Fin m} where mutual
  walk : {t : Tm m}
    → x ∈ₜ t → Steps m
  walk (here x)                      = []
  walk (ops {suc _} {i} {t ∷ ts} x∈) = walkTms i t [] ts x∈  

  walkTms : l ʳ+ (suc k) ∈ D
    → (t : Tm m) (us : Tm m ^ l) (ts : Tm m ^ k)
    → (x∈ : x ∈ₜₛ t ∷ ts)
    → Steps m
  walkTms i t₀ us ts (head x∈) = 
    step i us ts ∷ walk x∈
  walkTms i t₀ us (t ∷ ts) (tail x∈) =
    walkTms i t (t₀ ∷ us) ts x∈

_≺_ : Tm m → Tm m → Set
_≺_ = _<_ on size

≺-wf : WellFounded (_≺_ {m})
≺-wf = On.wellFounded size <-wf 
