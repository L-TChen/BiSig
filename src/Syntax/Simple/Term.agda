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

pattern op′ i ts = op (i , ts)

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

length∈ᵥₛ : {x : Fin Θ} {ts : Tm Θ ^ n} → x ∈ᵥₛ ts → Fin n
length∈ᵥₛ (head x∈) = zero
length∈ᵥₛ (tail x∈) = suc (length∈ᵥₛ x∈)

lookup∈ᵥₛ : {x : Fin Θ} {ts : Tm Θ ^ n}
  → (i : x ∈ᵥₛ ts)
  → x ∈ᵥ lookup ts (length∈ᵥₛ i) 
lookup∈ᵥₛ (head x∈) = x∈
lookup∈ᵥₛ (tail x∈) = lookup∈ᵥₛ x∈

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
Sub Θ n = Vec (Tm n) Θ

module _ (σ : Sub Θ n) where mutual
  sub : Tm Θ → Tm n
  sub (` x)         = lookup σ x
  sub (op (i , ts)) = op (i , subⁿ ts)

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


{-
------------------------------------------------------------------------------
-- Partial Substitution

PSub : (Ξ Θ : ℕ) → Set₁
PSub Ξ Θ = Σ[ P ∈ (Fin Ξ → Set) ] Σ[ σ ∈ ({i : Fin Ξ} → P i → Tm Θ) ]
  ({i : Fin Ξ} (x y : P i) → σ x ≡ σ y)

module _ ((P , σ , well-defined) : PSub Ξ Θ) where mutual
  psub : (t : Tm Ξ) → (∀ {i} → i ∈ᵥ t → P i)
    → Tm Θ
  psub (` x)  p = σ (p (here refl))
  psub (op (_ , i , ts)) p = op (_ , i , psubⁿ ts (p ∘ op))

  psubⁿ : (ts : Tm Ξ ^ n) → (∀ {i} → i ∈ᵥₛ ts → P i)
    → Tm Θ ^ n 
  psubⁿ []       p = []
  psubⁿ (t ∷ ts) p = psub t (p ∘ head) ∷ psubⁿ ts (p ∘ tail)

module _ {Ξ : ℕ} where
  _∪?_ : ((P₁ , σ₁ , p₁) (P₂ , σ₂ , p₂) : PSub Ξ Θ)
    → Dec (∀ i → (x : P₁ i) (y : P₂ i) → σ₁ x ≡ σ₂ y)
    --→ Dec (Σ[ (P , σ , p) ∈ PSub Ξ Θ ] Σ[ P=P₁+P₂ ∈ (∀ i → P i ⇔ (P₁ i ⊎ P₂ i)) ]
    --    (∀ {i} → (x : P i) → [ (λ y → σ x ≡ σ₁ y) , (λ z → σ x ≡ σ₂ z) ]
    --      (P=P₁+P₂ i .Equivalence.to x)))
    --    -- σ x ≡ {!!} ⊎ {!!}))
  (P₁ , σ₁ , p₁) ∪? (P₂ , σ₂ , p₂) = {!!}

record _and_ (P Q : Prop) : Prop where
  field
    fst : P
    snd : Q

module _ ((P , σ) : PSub Ξ Θ) where mutual
  psub : (t : Tm Ξ) → (∀ {i} → i ∈ᵥ t → P i)
    → Tm Θ
  psub (` x)             p = σ (p (here refl))  
  psub (op (_ , i , ts)) p = op (_ , i , psubⁿ ts λ i∈ → p (op i∈))

  psubⁿ : (ts : Tm Ξ ^ n) → (∀ {i} → i ∈ᵥₛ ts → P i)
    → Tm Θ ^ n
  psubⁿ []       _ = []
  psubⁿ (t ∷ ts) p = psub t (λ i∈ → p (head i∈)) ∷ psubⁿ ts λ i∈ → p (tail i∈)

_∪_ : ((P₁ , σ₁) (P₂ , σ₂) : PSub Ξ Θ)
  → Dec (Σ (PSub Ξ Θ) λ (P , σ) → {!(i : Fin Ξ) → P i → P₁ i and P₂ i !})
_∪_ = {!!}

∈ᵥ-≡ : {i x : Fin Ξ}
  → ∥ i ∈ᵥ ` x ∥ → ∥ i ≡ x ∥
∈ᵥ-≡ = squash-map λ where (here x) → x

∉[] : {i : Fin Ξ}
  → ∥ i ∈ᵥₛ [] ∥ → ⊥ₚ
∉[] ∣ () ∣
module _ {Ξ Θ : ℕ} where mutual
  eq : (t : Tm Ξ) (u : Tm Θ)
    → Maybe ({ i : Fin Ξ} → ∥ i ∈ᵥ t ∥  → Tm Θ)
  eq (` x)  u = just λ {i} p → case i ≟ x of λ where
    (yes eq) → u
    (no neq) → ⊥-elimₚ (refutingₚ neq (∈ᵥ-≡ p))
  eq (op (_ , i , _)) (` _)            = nothing
  eq (op (_ , i , ts)) (op (_ , j , us)) with i ≟∈ j
  ... | no ¬p = nothing
  ... | yes refl with eqⁿ ts us
  ... | nothing = nothing
  ... | just σ  = just λ i∈ → σ (squash-map (λ {(op x∈) → x∈}) i∈)

  eqⁿ : (ts : Tm Ξ ^ n) (us : Tm Θ ^ n)
    → Maybe ({i : Fin Ξ} → ∥ i ∈ᵥₛ ts ∥ → Tm Θ)
  eqⁿ []       []       = just λ bot → ⊥-elimₚ (∉[] bot)
  eqⁿ (t ∷ ts) (u ∷ us) with eq t u
  ... | nothing = nothing
  ... | just σ  with eqⁿ ts us
  ... | nothing = nothing
  ... | just σ′ = {!!}

-}
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

instance
  TmEquality : DecEq (Tm Θ)
  TmEquality = record { _≟_ = _≟ₜ_ }
