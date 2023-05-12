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
  op : ⟦ D ⟧ (Tm n) → Tm n -- Σ_{m ∈ Ds} (Vec (Tm n) m) → Tm n

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

-- [TODO] Generalise it to an Any predicate
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

------------------------------------------------------------------------------
-- Substitution structure

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
  
Ren-id : Ren m m
Ren-id = allFin _

Ren-⨟  : Ren m n → Ren n l → Ren m l
Ren-⨟ σ₁ σ₂ = tabulate $ lookup σ₂ ∘ lookup σ₁

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

Sub-id : Sub m m
Sub-id = tabulate `_

RenToSub : Ren m n → Sub m n
RenToSub σ = map `_ σ

Sub-⨟ : Sub m n → Sub n l → Sub m l
Sub-⨟ σ₁ σ₂ = tabulate λ i → sub σ₂ (lookup σ₁ i)

sub-for : (Tm m) → (x y : Fin (suc m)) → Tm m
sub-for t x y with x ≟ y
... | no ¬p = ` punchOut ¬p
... | yes _ = t

_for_
  : Tm m → Fin (suc m)
  → Sub (suc m) m
t for x = tabulate (sub-for t x)

injectˡ : Ren m (m + n)
injectˡ = tabulate λ i → _↑ˡ_ i _

wkʳ : Tm m → Tm (n + m)
wkʳ = rename $ tabulate (_↑ʳ_ _)

wkˡ : Tm m → Tm (m + n)
wkˡ = rename injectˡ

wkᵐ : (m n : ℕ) → Tm (m + l) → Tm (m + n + l)
wkᵐ m n = rename $ tabulate (insert-mid m n)

wk≤ˡ : m ≤ n → Tm m → Tm n
wk≤ˡ (less-than-or-equal refl) = wkˡ

weaken : Tm m → Tm (suc m)
weaken = rename $ tabulate suc

mutual
  punchOutTm : {x : Fin (suc n)} {t : Tm (suc n)}
    → ¬ x ∈ₜ t → Tm n
  punchOutTm {_} {x} {` y}  x∉ = ` punchOut (x∉ ∘ here)
  punchOutTm {_} {x} {op (_ , i , ts)} x∉ =
    op (_ , i , punchOutTmⁿ (x∉ ∘ ops))

  punchOutTmⁿ : {x : Fin (suc Ξ)} {ts : Tm (suc Ξ) ^ n}
    → ¬ x ∈ₜₛ ts → Tm Ξ ^ n
  punchOutTmⁿ {ts = []}     _  = []
  punchOutTmⁿ {ts = t ∷ ts} x∉ =
    punchOutTm (x∉ ∘ head) ∷ punchOutTmⁿ (x∉ ∘ tail)

punchInTm : (x : Fin (suc m))
  → Tm m → Tm (suc m)
punchInTm x = rename (tabulate (punchIn x))

punchInTmⁿ : (x : Fin (suc m))
  → Tm m ^ k → Tm (suc m) ^ k
punchInTmⁿ x = renameⁿ (tabulate (punchIn x))

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

plugSteps : Steps m → Sub m n → Steps n
plugSteps []       σ  = []
plugSteps (step pos us ts ∷ ps) σ =
  step pos (subⁿ σ us) (subⁿ σ ts) ∷ plugSteps ps σ

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

------------------------------------------------------------------------------
-- Instances of Presheaves 

open ≡-Reasoning

module _ {m : ℕ} where mutual
  rename-id : (t : Tm m)
    → rename Ren-id t ≡ t
  rename-id (` x)      = cong `_ (lookup∘tabulate (λ i → i) x)
  rename-id (op′ i ts) = cong (op′ i) (renameⁿ-id ts)

  renameⁿ-id : (ts : Tm m ^ l)
    → renameⁿ Ren-id ts ≡ ts
  renameⁿ-id []       = refl
  renameⁿ-id (t ∷ ts) = cong₂ _∷_ (rename-id t) (renameⁿ-id ts)

module _ {m : ℕ} (σ : Ren m n) (ρ : Ren n l) where mutual
  rename-⨟ : (t : Tm m)
    → rename (Ren-⨟ σ ρ) t ≡ rename ρ (rename σ t)
  rename-⨟ (` x)      = cong `_ (lookup∘tabulate (lookup ρ ∘ lookup σ) x)
  rename-⨟ (op′ i ts) = cong (op′ i) (renameⁿ-⨟ ts)

  renameⁿ-⨟ : (ts : Tm m ^ k)
    → renameⁿ (Ren-⨟ σ ρ) ts ≡ renameⁿ ρ (renameⁿ σ ts)
  renameⁿ-⨟ []       = refl
  renameⁿ-⨟ (t ∷ ts) = cong₂ _∷_ (rename-⨟ t) (renameⁿ-⨟ ts)

Ren-assoc
  : (σ : Ren m n) (ρ : Ren n l) (γ : Ren l k)
  → Ren-⨟ (Ren-⨟ σ ρ) γ ≡ Ren-⨟ σ (Ren-⨟ ρ γ)
Ren-assoc σ ρ γ = tabulate-cong (λ i → begin
  lookup γ (lookup (Ren-⨟ σ ρ) i)  -- ` i ⟨ σ ⨟ ρ ⟩ ⟨ γ ⟩
    ≡⟨ cong (lookup γ) (lookup∘tabulate (lookup ρ ∘ lookup σ) i) ⟩
  lookup γ (lookup ρ (lookup σ i))
    ≡⟨ (sym $ lookup∘tabulate (lookup γ ∘ lookup ρ) (lookup σ i)) ⟩
  lookup (tabulate (λ i → lookup γ (lookup ρ i))) (lookup σ i)
    ∎)
    
module _ {m : ℕ} where mutual
  sub-id : (t : Tm m)
    → sub Sub-id t ≡ t
  sub-id (` x)      = lookup∘tabulate `_ x
  sub-id (op′ i ts) = cong (op′ i) (subⁿ-id ts)

  subⁿ-id : (t : Tm m ^ l)
    → subⁿ Sub-id t ≡ t
  subⁿ-id []       = refl
  subⁿ-id (t ∷ ts) =
    cong₂ _∷_ (sub-id t) (subⁿ-id ts)

module _ {m n l : ℕ} (σ : Sub m n) (ρ : Sub n l) where mutual
  sub-⨟ : (t : Tm m)
    → sub (Sub-⨟ σ ρ) t ≡ sub ρ (sub σ t)
  sub-⨟ (` x)      = lookup∘tabulate (λ i → sub ρ (lookup σ i)) x
  sub-⨟ (op′ i ts) = cong (λ ts → op′ i ts) (subⁿ-⨟ ts)

  subⁿ-⨟ : (ts : Tm m ^ k)
    → subⁿ (Sub-⨟ σ ρ) ts ≡ subⁿ ρ (subⁿ σ ts)
  subⁿ-⨟ {zero}  []       = refl
  subⁿ-⨟ {suc k} (t ∷ ts) = cong₂ _∷_ (sub-⨟ t) (subⁿ-⨟ ts)

Sub-assoc
  : (σ : Sub m n) (ρ : Sub n l) (γ : Sub l k)
  → Sub-⨟ (Sub-⨟ σ ρ) γ ≡ Sub-⨟ σ (Sub-⨟ ρ γ)
Sub-assoc σ ρ γ = tabulate-cong (λ i → begin
  sub γ (sub (Sub-⨟ σ ρ) (` i)) 
    ≡⟨ cong (sub γ ) (sub-⨟ σ ρ (` i)) ⟩
  sub γ (sub ρ (sub σ (` i)))
    ≡⟨ sym $ sub-⨟ ρ γ (sub σ $ ` i) ⟩
  sub (Sub-⨟ ρ γ) (sub σ (` i))
    ∎)

instance
  RenIsCategory : IsCategory ℕ Ren
  RenIsCategory .id      = Ren-id
  RenIsCategory ._⨟_     = Ren-⨟
  RenIsCategory .⨟-assoc = Ren-assoc
  RenIsCategory .⨟-idᵣ σ = begin
    σ ⨟ id
      ≡⟨ tabulate-cong (λ i → lookup∘tabulate (λ i → i) (lookup σ i)) ⟩
    tabulate (λ x → lookup σ x)
      ≡⟨ tabulate∘lookup σ ⟩
    σ
      ∎
  RenIsCategory .⨟-idₗ σ = begin
    id ⨟ σ
      ≡⟨ tabulate-cong (λ i → cong (lookup σ) (lookup∘tabulate (λ i → i) i)) ⟩
    tabulate (λ i → lookup σ i)
      ≡⟨ tabulate∘lookup σ ⟩
    σ
      ∎

  SubIsCategory : IsCategory ℕ Sub
  SubIsCategory .id      = Sub-id
  SubIsCategory ._⨟_     = Sub-⨟ 
  SubIsCategory .⨟-assoc = Sub-assoc
  SubIsCategory .⨟-idᵣ σ = begin
    σ ⨟ id
      ≡⟨ tabulate-cong (λ i → sub-id (lookup σ i)) ⟩
    tabulate (λ i → lookup σ i) 
      ≡⟨ tabulate∘lookup σ ⟩
    σ
      ∎
  SubIsCategory .⨟-idₗ σ = begin
    id ⨟ σ
      ≡⟨ tabulate-cong (λ i → cong (sub σ) (sub-id (` i))) ⟩
    tabulate (λ i → sub σ (` i))
      ≡⟨ tabulate∘lookup σ ⟩
    σ
      ∎

module _ {m : ℕ} where mutual
  plugSteps-id : (ps : Steps m)
    → plugSteps ps id ≡ ps
  plugSteps-id []       = refl
  plugSteps-id (step p us ts ∷ ps) = cong₂ _∷_
    (cong₂ (step p) (subⁿ-id us) (subⁿ-id ts))
    (plugSteps-id ps)

module _ {m n l : ℕ} (σ : Sub m n) (ρ : Sub n l) where mutual
  plugSteps-⨟ : (ps : Steps m)
    → plugSteps ps (σ ⨟ ρ) ≡ plugSteps (plugSteps ps σ) ρ
  plugSteps-⨟ []       = refl
  plugSteps-⨟ (step p ts us ∷ ps) = cong₂ _∷_
    (cong₂ (step p) (subⁿ-⨟ σ ρ ts ) (subⁿ-⨟ σ ρ us))
    (plugSteps-⨟ ps)

instance
  TmRenIsPresheaf : IsPresheaf Tm
  TmRenIsPresheaf ._⟨_⟩ t ρ = rename ρ t
  TmRenIsPresheaf .⟨⟩-id t    = rename-id t
  TmRenIsPresheaf .⟨⟩-⨟ σ ρ t = rename-⨟ σ ρ t 

  TmsRenIsPresheaf : IsPresheaf (λ m → Tm m ^ l)
  TmsRenIsPresheaf ._⟨_⟩ ts ρ = renameⁿ ρ ts
  TmsRenIsPresheaf .⟨⟩-id ts    = renameⁿ-id ts
  TmsRenIsPresheaf .⟨⟩-⨟ σ ρ ts = renameⁿ-⨟ σ ρ ts

  TmSubIsPresheaf : IsPresheaf Tm
  TmSubIsPresheaf ._⟨_⟩ t σ = sub σ t
  TmSubIsPresheaf .⟨⟩-id = sub-id
  TmSubIsPresheaf .⟨⟩-⨟  = sub-⨟

  TmsSubIsPresheaf : IsPresheaf (λ m → Tm m ^ k)
  TmsSubIsPresheaf ._⟨_⟩ t σ = subⁿ σ t
  TmsSubIsPresheaf .⟨⟩-id       = subⁿ-id
  TmsSubIsPresheaf .⟨⟩-⨟ σ ρ ts = subⁿ-⨟ σ ρ ts

  plugSubIsPresheaf : IsPresheaf Steps
  plugSubIsPresheaf ._⟨_⟩ = plugSteps
  plugSubIsPresheaf .⟨⟩-id       = plugSteps-id
  plugSubIsPresheaf .⟨⟩-⨟ σ ρ ts = plugSteps-⨟ σ ρ ts
