{-# OPTIONS --with-K --safe #-}

open import Prelude
open import Syntax.Simple.Description


module Syntax.Simple.Term (D : Desc) where

import Relation.Binary.Construct.On as On

private variable
  Ξ Θ Θ₁ Θ₂ Θ₃ : ℕ
  m n k i : ℕ
  A B : Set

infix 9 `_
data Tm (Θ : ℕ) : Set where
  `_ :       Fin Θ  → Tm Θ
  op : ⟦ D ⟧ (Tm Θ) → Tm Θ

pattern op′ i ts = op (_ , i , ts)

Tm₀ : Set
Tm₀ = Tm 0

Tms : ℕ → Set
Tms Θ = List (Tm Θ)

Tms₀ : Set
Tms₀ = List Tm₀

module _ {X : ℕ → Set} (α : (D -Alg) X) where mutual
  fold : Tm ⇒₁ X
  fold (` x)             = α .var x
  fold (op (_ , i , ts)) = α .alg (_ , i , foldⁿ ts)

  foldⁿ : {l : ℕ} → Tm Θ ^ l → X Θ ^ l
  foldⁿ []       = []
  foldⁿ (t ∷ ts) = fold t ∷ foldⁿ ts

mutual
  fv : Tm Θ → List (Fin Θ)
  fv (` x)             = x ∷ []
  fv (op (n , i , ts)) = fvⁿ ts

  fvⁿ : Tm Θ ^ n → List (Fin Θ)
  fvⁿ []       = []
  fvⁿ (t ∷ ts) = fv t ++ fvⁿ ts

mutual
  size : Tm Θ → ℕ
  size (` x)      = 1
  size (op′ _ ts) = suc (sizeⁿ ts)

  sizeⁿ : Tm Θ ^ n → ℕ
  sizeⁿ []       = 0
  sizeⁿ (t ∷ ts) = size t + sizeⁿ ts

mutual
  _≟ₜ_ : (t u : Tm Θ) → Dec (t ≡ u)
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

  compareMap : (ts us : Tm Θ ^ n) → Dec (ts ≡ us)
  compareMap []       []        = yes refl
  compareMap (t ∷ ts) (u ∷ us) with t ≟ₜ u
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes p with compareMap ts us
  ... | no ¬q = no λ where refl → ¬q refl
  ... | yes q = yes (cong₂ _∷_ p q)

-- [TODO] Generalise it to an Any predicate
infix 4 _∈ₜ_ _∈ₜₛ_ _∈ₜ?_ _∈ₜₛ?_ _∉ₜ_ _∉ₜₛ_

mutual
  data _∈ₜ_ (x : Fin Θ) : Tm Θ → Set where
    here : {y : Fin Θ} → x ≡ y → x ∈ₜ ` y
    ops  : {n : ℕ} {i : n ∈ D} {ts : Tm Θ ^ n}
      → (x∈ : x ∈ₜₛ ts) → x ∈ₜ op (n , i , ts)

  data _∈ₜₛ_ (x : Fin Θ) : Tm Θ ^ n → Set where
    head : {t : Tm Θ} {ts : Tm Θ ^ n}
      → (x∈ : x ∈ₜ t) → x ∈ₜₛ (t ∷ ts)
    tail : {t : Tm Θ} {ts : Tm Θ ^ n}
      → (x∈ : x ∈ₜₛ ts)
      → x ∈ₜₛ (t ∷ ts)

_∉ₜ_ : (x : Fin Θ) → Tm Θ → Set
x ∉ₜ t = ¬ x ∈ₜ t

_∉ₜₛ_ : (x : Fin Θ) → Tm Θ ^ n → Set
x ∉ₜₛ ts = ¬ x ∈ₜₛ ts

mutual
  _∈ₜ?_ : (x : Fin Θ) (t : Tm Θ) → Dec (x ∈ₜ t)
  x ∈ₜ? ` y with x ≟ y
  ... | yes p = yes (here p)
  ... | no ¬p = no λ where (here p) → ¬p p
  x ∈ₜ? op (_ , _ , ts) with x ∈ₜₛ? ts
  ... | yes p = yes (ops p)
  ... | no ¬p = no λ where
    (ops x∈) → ¬p x∈

  _∈ₜₛ?_ : (x : Fin Θ) (ts : Tm Θ ^ n) → Dec (x ∈ₜₛ ts)
  _∈ₜₛ?_ {_} x [] = no λ ()
  _∈ₜₛ?_ {_} x (t ∷ ts) with x ∈ₜ? t
  ... | yes p = yes (head p)
  ... | no ¬p with x ∈ₜₛ? ts
  ... | yes q = yes (tail q)
  ... | no ¬q = no λ where
    (head x∈) → ¬p x∈
    (tail x∈) → ¬q x∈

length∈ₜₛ : {x : Fin Θ} {ts : Tm Θ ^ n} → x ∈ₜₛ ts → Fin n
length∈ₜₛ (head x∈) = zero
length∈ₜₛ (tail x∈) = suc (length∈ₜₛ x∈)

lookup∈ₜₛ : {x : Fin Θ} {ts : Tm Θ ^ n}
  → (i : x ∈ₜₛ ts)
  → x ∈ₜ lookup ts (length∈ₜₛ i)
lookup∈ₜₛ (head x∈) = x∈
lookup∈ₜₛ (tail x∈) = lookup∈ₜₛ x∈

------------------------------------------------------------------------------
-- Substitution structure

Ren : ℕ → ℕ → Set
Ren Θ n = Fin Θ → Fin n -- Vec (Fin n) m

module _ (ρ : Ren Θ n) where mutual
  rename : Tm Θ → Tm n
  rename (` x)             = ` ρ x -- ` lookup ρ x
  rename (op (_ , i , ts)) = op (_ , i , renameⁿ ts)

  renameⁿ : {l : ℕ}
    → Tm Θ ^ l → Tm n ^ l
  renameⁿ []        = []
  renameⁿ (t ∷ ts) = rename t ∷ renameⁿ ts

Ren-id : Ren Θ Θ
Ren-id = λ i → i -- allFin _

Ren-⨟  : Ren Θ₁ Θ₂ → Ren Θ₂ Θ₃ → Ren Θ₁ Θ₃
Ren-⨟ σ₁ σ₂ = σ₂ ∘ σ₁ -- tabulate $ lookup σ₂ ∘ lookup σ₁

Sub : (Θ n : ℕ) → Set
Sub Θ n = Vec (Tm n) Θ

module _ (σ : Sub Θ n) where mutual
  sub : Tm Θ → Tm n
  sub (` x)  = lookup σ x
  sub (op (_ , i , ts)) = op (_ , i , subⁿ ts)

  subⁿ : {l : ℕ}
    → Tm Θ ^ l → Tm n ^ l
  subⁿ []       = []
  subⁿ (t ∷ ts) = sub t ∷ subⁿ ts

Sub-id : Sub Θ Θ
Sub-id = tabulate `_

RenToSub : Ren Θ n → Sub Θ n
RenToSub σ = tabulate (`_ ∘ σ) -- V.map `_ σ

opaque
  Sub-⨟ : Sub Θ₁ Θ₂ → Sub Θ₂ Θ₃ → Sub Θ₁ Θ₃
  Sub-⨟ σ₁ σ₂ = tabulate λ i → sub σ₂ (lookup σ₁ i)

  sub-for : (Tm Θ) → (x y : Fin (suc Θ)) → Tm Θ
  sub-for t x y with x ≟ y
  ... | no ¬p = ` punchOut ¬p
  ... | yes _ = t

  _for_
    : Tm Θ → Fin (suc Θ)
    → Sub (suc Θ) Θ
  t for x = tabulate (sub-for t x)

  injectˡ : Ren Θ (Θ + n)
  injectˡ = λ i → _↑ˡ_ i _ -- tabulate λ i → _↑ˡ_ i _

{-
wkʳ : Tm Θ → Tm (i + Θ)
wkʳ = rename (_↑ʳ_ _) -- rename $ tabulate (_↑ʳ_ _)

wkˡ : Tm Θ → Tm (Θ + i)
wkˡ = rename injectˡ

wkˡⁿ : Tm Θ ^ l → Tm (Θ + i) ^ l
wkˡⁿ = renameⁿ injectˡ

wkᵐ : (Θ i : ℕ) → Tm (Θ + l) → Tm (Θ + i + l)
wkᵐ m n = rename (insert-mid m n) -- rename $ tabulate (insert-mid m n)

wk≤ˡ : Θ ≤ n → Tm Θ → Tm n
wk≤ˡ (less-than-or-equal refl) = wkˡ

weaken : Tm Θ → Tm (suc Θ)
weaken = rename suc -- rename $ tabulate suc
-}
mutual
  punchOutTm : {x : Fin (suc Θ)} {t : Tm (suc Θ)}
    → ¬ x ∈ₜ t → Tm Θ
  punchOutTm {_} {x} {` y}  x∉ = ` punchOut (x∉ ∘ here)
  punchOutTm {_} {x} {op (_ , i , ts)} x∉ =
    op (_ , i , punchOutTmⁿ (x∉ ∘ ops))

  punchOutTmⁿ : {x : Fin (suc Θ)} {ts : Tm (suc Θ) ^ n}
    → ¬ x ∈ₜₛ ts → Tm Θ ^ n
  punchOutTmⁿ {ts = []}     _  = []
  punchOutTmⁿ {ts = t ∷ ts} x∉ =
    punchOutTm (x∉ ∘ head) ∷ punchOutTmⁿ (x∉ ∘ tail)

punchInTm : (x : Fin (suc Θ))
  → Tm Θ → Tm (suc Θ)
punchInTm x = rename (punchIn x)-- rename (tabulate (punchIn x))

punchInTmⁿ : (x : Fin (suc Θ))
  → Tm Θ ^ n → Tm (suc Θ) ^ n
punchInTmⁿ x = renameⁿ (punchIn x) -- renameⁿ (tabulate (punchIn x))

------------------------------------------------------------------------------
-- Zipper for Simple Terms

record Step (Θ : ℕ) : Set where
  constructor step
  field
    {iᵤ iₜ} : ℕ
    pos : iᵤ ʳ+ suc iₜ ∈ D
    us  : Tm Θ ^ iᵤ
    ts  : Tm Θ ^ iₜ
open Step public using ()

Steps : ℕ → Set
Steps Θ = List (Step Θ)

plugSteps : Steps Θ₁ → Sub Θ₁ Θ₂ → Steps Θ₂
plugSteps []       σ  = []
plugSteps (step pos us ts ∷ ps) σ =
  step pos (subⁿ σ us) (subⁿ σ ts) ∷ plugSteps ps σ

infixr 4.5 _▷₁_ _▷_

_▷₁_ : Step Θ → Tm Θ → Tm Θ
step i us ts ▷₁ t = op′ i $ us ʳ++ (t ∷ ts)

_▷_ : Steps Θ → Tm Θ → Tm Θ
[]       ▷ t = t
(p ∷ ps) ▷ t = p ▷₁ (ps ▷ t)

module _ {x : Fin Θ} where mutual
  walk : {t : Tm Θ}
    → x ∈ₜ t → Steps Θ
  walk (here x)                      = []
  walk (ops {suc _} {i} {t ∷ ts} x∈) = walkTms i t [] ts x∈

  walkTms : m ʳ+ (suc n) ∈ D
    → (t : Tm Θ) (us : Tm Θ ^ m) (ts : Tm Θ ^ n)
    → (x∈ : x ∈ₜₛ t ∷ ts)
    → Steps Θ
  walkTms i t₀ us ts (head x∈) =
    step i us ts ∷ walk x∈
  walkTms i t₀ us (t ∷ ts) (tail x∈) =
    walkTms i t (t₀ ∷ us) ts x∈

_≺_ : Tm Θ → Tm Θ → Set
_≺_ = _<_ on size

≺-wf : WellFounded (_≺_ {Θ})
≺-wf = On.wellFounded size <-wf

------------------------------------------------------------------------------
-- Instances of Presheaves

open ≡-Reasoning

module _ {Θ : ℕ} where mutual
  rename-id : (t : Tm Θ)
    → rename Ren-id t ≡ t
  rename-id (` x)      = refl -- cong `_ (lookup∘tabulate (λ i → i) x)
  rename-id (op′ i ts) = cong (op′ i) (renameⁿ-id ts)

  renameⁿ-id : (ts : Tm Θ ^ n)
    → renameⁿ Ren-id ts ≡ ts
  renameⁿ-id []       = refl
  renameⁿ-id (t ∷ ts) = cong₂ _∷_ (rename-id t) (renameⁿ-id ts)

module _ (σ : Ren Θ₁ Θ₂) (ρ : Ren Θ₂ Θ₃) where mutual
  rename-⨟ : (t : Tm Θ₁)
    → rename (Ren-⨟ σ ρ) t ≡ rename ρ (rename σ t)
  rename-⨟ (` x)      = refl -- cong `_ (lookup∘tabulate (lookup ρ ∘ lookup σ) x)
  rename-⨟ (op′ i ts) = cong (op′ i) (renameⁿ-⨟ ts)

  renameⁿ-⨟ : (ts : Tm Θ₁ ^ k)
    → renameⁿ (Ren-⨟ σ ρ) ts ≡ renameⁿ ρ (renameⁿ σ ts)
  renameⁿ-⨟ []       = refl
  renameⁿ-⨟ (t ∷ ts) = cong₂ _∷_ (rename-⨟ t) (renameⁿ-⨟ ts)

Ren-assoc
  : (σ : Ren Θ₁ Θ₂) (ρ : Ren Θ₂ Θ₃) (γ : Ren Θ₃ Θ)
  → Ren-⨟ (Ren-⨟ σ ρ) γ ≡ Ren-⨟ σ (Ren-⨟ ρ γ)
Ren-assoc σ ρ γ = refl
  {- tabulate-cong (λ i → begin
  lookup γ (lookup (Ren-⨟ σ ρ) i)  -- ` i ⟨ σ ⨟ ρ ⟩ ⟨ γ ⟩
    ≡⟨ cong (lookup γ) (lookup∘tabulate (lookup ρ ∘ lookup σ) i) ⟩
  lookup γ (lookup ρ (lookup σ i))
    ≡⟨ (sym $ lookup∘tabulate (lookup γ ∘ lookup ρ) (lookup σ i)) ⟩
  lookup (tabulate (λ i → lookup γ (lookup ρ i))) (lookup σ i)
    ∎)
  -}

module _ {Θ : ℕ} where mutual
  sub-id : (t : Tm Θ)
    → sub Sub-id t ≡ t
  sub-id (` x)      = lookup∘tabulate `_ x
  sub-id (op′ i ts) = cong (op′ i) (subⁿ-id ts)

  subⁿ-id : (t : Tm Θ ^ n)
    → subⁿ Sub-id t ≡ t
  subⁿ-id []       = refl
  subⁿ-id (t ∷ ts) =
    cong₂ _∷_ (sub-id t) (subⁿ-id ts)

module _ {Θ n l : ℕ} (σ : Sub Θ n) (ρ : Sub n l) where opaque
  unfolding Sub-⨟
  mutual
    sub-⨟ : (t : Tm Θ)
      → sub (Sub-⨟ σ ρ) t ≡ sub ρ (sub σ t)
    sub-⨟ (` x)      = lookup∘tabulate (λ i → sub ρ (lookup σ i)) x
    sub-⨟ (op′ i ts) = cong (λ ts → op′ i ts) (subⁿ-⨟ ts)

    subⁿ-⨟ : (ts : Tm Θ ^ k)
      → subⁿ (Sub-⨟ σ ρ) ts ≡ subⁿ ρ (subⁿ σ ts)
    subⁿ-⨟ {zero}  []       = refl
    subⁿ-⨟ {suc k} (t ∷ ts) = cong₂ _∷_ (sub-⨟ t) (subⁿ-⨟ ts)

opaque
  unfolding Sub-⨟

  Sub-assoc
    : (σ : Sub Θ Θ₁) (ρ : Sub Θ₁ Θ₂) (γ : Sub Θ₂ Θ₃)
    → Sub-⨟ (Sub-⨟ σ ρ) γ ≡ Sub-⨟ σ (Sub-⨟ ρ γ)
  Sub-assoc σ ρ γ = tabulate-cong (λ i → begin
    sub γ (sub (Sub-⨟ σ ρ) (` i))
      ≡⟨ cong (sub γ ) (sub-⨟ σ ρ (` i)) ⟩
    sub γ (sub ρ (sub σ (` i)))
      ≡⟨ sym $ sub-⨟ ρ γ (sub σ $ ` i) ⟩
    sub (Sub-⨟ ρ γ) (sub σ (` i))
      ∎)

  Sub-⨟-idᵣ : (σ : Sub Θ n)
    → Sub-⨟ σ Sub-id ≡ σ
  Sub-⨟-idᵣ σ = begin
    Sub-⨟ σ Sub-id
      ≡⟨ tabulate-cong (λ i → sub-id (lookup σ i)) ⟩
    tabulate (λ i → lookup σ i)
      ≡⟨ tabulate∘lookup σ ⟩
    σ
      ∎

  Sub-⨟-idₗ : (σ : Sub Θ n) → Sub-⨟ Sub-id σ ≡ σ
  Sub-⨟-idₗ σ = begin
    Sub-⨟ Sub-id σ
      ≡⟨ tabulate-cong (λ i → cong (sub σ) (sub-id (` i))) ⟩
    tabulate (λ i → sub σ (` i))
      ≡⟨ tabulate∘lookup σ ⟩
    σ
      ∎

instance
  RenIsCategory : IsCategory ℕ Ren
  RenIsCategory .id      = Ren-id -- Ren-id
  RenIsCategory ._⨟_     = Ren-⨟
  RenIsCategory .⨟-assoc = Ren-assoc
  RenIsCategory .⨟-idᵣ σ = refl
  {-
    begin
    σ ⨟ id
      ≡⟨ tabulate-cong (λ i → lookup∘tabulate (λ i → i) (lookup σ i)) ⟩
    tabulate (λ x → lookup σ x)
      ≡⟨ tabulate∘lookup σ ⟩
    σ
      ∎
   -}
  RenIsCategory .⨟-idₗ σ = refl
  {- begin
    id ⨟ σ
      ≡⟨ tabulate-cong (λ i → cong (lookup σ) (lookup∘tabulate (λ i → i) i)) ⟩
    tabulate (lookup σ)
      ≡⟨ tabulate∘lookup σ ⟩
    σ
      ∎
  -}

  SubIsCategory : IsCategory ℕ Sub
  SubIsCategory .id      = Sub-id
  SubIsCategory ._⨟_     = Sub-⨟
  SubIsCategory .⨟-assoc = Sub-assoc
  SubIsCategory .⨟-idᵣ   = Sub-⨟-idᵣ
  SubIsCategory .⨟-idₗ   = Sub-⨟-idₗ

module _ {Θ : ℕ} where mutual
  plugSteps-id : (ps : Steps Θ)
    → plugSteps ps id ≡ ps
  plugSteps-id []       = refl
  plugSteps-id (step p us ts ∷ ps) = cong₂ _∷_
    (cong₂ (step p) (subⁿ-id us) (subⁿ-id ts))
    (plugSteps-id ps)

module _ {Θ n l : ℕ} (σ : Sub Θ n) (ρ : Sub n l) where mutual
  plugSteps-⨟ : (ps : Steps Θ)
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

  TmsRenIsPresheaf : IsPresheaf (λ Θ → Tm Θ ^ n)
  TmsRenIsPresheaf ._⟨_⟩ ts ρ = renameⁿ ρ ts
  TmsRenIsPresheaf .⟨⟩-id ts    = renameⁿ-id ts
  TmsRenIsPresheaf .⟨⟩-⨟ σ ρ ts = renameⁿ-⨟ σ ρ ts

  TmSubIsPresheaf : IsPresheaf Tm
  TmSubIsPresheaf ._⟨_⟩ t σ = sub σ t
  TmSubIsPresheaf .⟨⟩-id = sub-id
  TmSubIsPresheaf .⟨⟩-⨟  = sub-⨟

  TmsSubIsPresheaf : IsPresheaf (λ Θ → Tm Θ ^ n)
  TmsSubIsPresheaf ._⟨_⟩ t σ = subⁿ σ t
  TmsSubIsPresheaf .⟨⟩-id       = subⁿ-id
  TmsSubIsPresheaf .⟨⟩-⨟ σ ρ ts = subⁿ-⨟ σ ρ ts

  plugSubIsPresheaf : IsPresheaf Steps
  plugSubIsPresheaf ._⟨_⟩ = plugSteps
  plugSubIsPresheaf .⟨⟩-id       = plugSteps-id
  plugSubIsPresheaf .⟨⟩-⨟ σ ρ ts = plugSteps-⨟ σ ρ ts

instance
  TmEquality : DecEq (Tm Θ)
  TmEquality = record { _≟_ = _≟ₜ_ }
