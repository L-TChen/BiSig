{-# OPTIONS #-}

open import Prelude
  hiding (_+_)
open import Syntax.Simple.Description

module Syntax.Simple.Properties (D : Desc) where

open import Syntax.Simple.Term        D

open N using (_+_)

open ≡-Reasoning

private variable
  Ξ Θ Θ₁ Θ₂ Θ₃ n : ℕ
  ts us   : Tm Θ ^ n
  σ₁ σ₂   : Sub Ξ Θ
  x y     : Fin Ξ
  t u v   : Tm Ξ

------------------------------------------------------------------------------
-- Instances of Presheaves 

open ≡-Reasoning

module _ {Θ : ℕ} where mutual
  rename-id : (t : Tm Θ)
    → rename Ren-id t ≡ t
  rename-id (` x)      = refl -- cong `_ (lookup∘tabulate (λ i → i) x)
  rename-id (op (i , ts)) = cong (op ∘ (i ,_)) (renameⁿ-id ts)

  renameⁿ-id : (ts : Tm Θ ^ n)
    → renameⁿ Ren-id ts ≡ ts
  renameⁿ-id []       = refl
  renameⁿ-id (t ∷ ts) = cong₂ _∷_ (rename-id t) (renameⁿ-id ts)

module _ (σ : Ren Θ₁ Θ₂) (ρ : Ren Θ₂ Θ₃) where mutual
  rename-⨟ : (t : Tm Θ₁)
    → rename (Ren-⨟ σ ρ) t ≡ rename ρ (rename σ t)
  rename-⨟ (` x)      = refl -- cong `_ (lookup∘tabulate (lookup ρ ∘ lookup σ) x)
  rename-⨟ (op (i , ts)) = cong (op ∘ (i ,_)) (renameⁿ-⨟ ts)

  renameⁿ-⨟ : (ts : Tm Θ₁ ^ n)
    → renameⁿ (Ren-⨟ σ ρ) ts ≡ renameⁿ ρ (renameⁿ σ ts)
  renameⁿ-⨟ []       = refl
  renameⁿ-⨟ (t ∷ ts) = cong₂ _∷_ (rename-⨟ t) (renameⁿ-⨟ ts)

Ren-assoc
  : (σ : Ren Θ₁ Θ₂) (ρ : Ren Θ₂ Θ₃) (γ : Ren Θ₃ Θ)
  → Ren-⨟ (Ren-⨟ σ ρ) γ ≡ Ren-⨟ σ (Ren-⨟ ρ γ)
Ren-assoc σ ρ γ = refl
    
module _ {Θ : ℕ} where mutual
  sub-id : (t : Tm Θ)
    → sub Sub-id t ≡ t
  sub-id (` x)         = refl -- lookup∘tabulate `_ x
  sub-id (op (i , ts)) = cong (op ∘ (i ,_)) (subⁿ-id ts)

  subⁿ-id : (t : Tm Θ ^ n)
    → subⁿ Sub-id t ≡ t
  subⁿ-id []       = refl
  subⁿ-id (t ∷ ts) =
    cong₂ _∷_ (sub-id t) (subⁿ-id ts)

module _ (σ : Sub Θ Θ₁) (ρ : Sub Θ₁ Θ₂) where
  mutual
    sub-⨟ : (t : Tm Θ)
      → sub (Sub-⨟ σ ρ) t ≡ sub ρ (sub σ t)
    sub-⨟ (` x)      = refl -- lookup∘tabulate (λ i → sub ρ (lookup σ i)) x
    sub-⨟ (op (i , ts)) = cong (op ∘ (i ,_) ) (subⁿ-⨟ ts)

    subⁿ-⨟ : (ts : Tm Θ ^ n)
      → subⁿ (Sub-⨟ σ ρ) ts ≡ subⁿ ρ (subⁿ σ ts)
    subⁿ-⨟ {zero}  []       = refl
    subⁿ-⨟ {suc k} (t ∷ ts) = cong₂ _∷_ (sub-⨟ t) (subⁿ-⨟ ts)

Sub-assoc
  : (σ : Sub Θ Θ₁) (ρ : Sub Θ₁ Θ₂) (γ : Sub Θ₂ Θ₃)
  → (i : Fin Θ)
  → (Sub-⨟ (Sub-⨟ σ ρ) γ) i ≡ (Sub-⨟ σ (Sub-⨟ ρ γ)) i
Sub-assoc σ ρ γ i = sym (sub-⨟ ρ γ (σ i))

Sub-⨟-idᵣ : (σ : Sub Θ n)
  → (i : Fin Θ)
  → Sub-⨟ σ Sub-id i ≡ σ i
Sub-⨟-idᵣ σ i = sub-id (σ i)

Sub-⨟-idₗ : (σ : Sub Θ n)
  → (i : Fin Θ)
  → Sub-⨟ Sub-id σ i ≡ σ i
Sub-⨟-idₗ σ i = refl

instance
  RenIsCategory : IsCategory ℕ Ren _≡_
  RenIsCategory .isEquivalence = ≡-isEquivalence
  RenIsCategory .id      = Ren-id
  RenIsCategory ._⨟_     = Ren-⨟
  RenIsCategory .⨟-assoc = Ren-assoc
  RenIsCategory .⨟-idᵣ σ = refl
  RenIsCategory .⨟-idₗ σ = refl

  SubIsCategory : IsCategory ℕ Sub _≗_
  SubIsCategory .isEquivalence = ≗-isEquivalence 
  SubIsCategory .id      = Sub-id
  SubIsCategory ._⨟_     = Sub-⨟ 
  SubIsCategory .⨟-assoc = Sub-assoc
  SubIsCategory .⨟-idᵣ   = Sub-⨟-idᵣ
  SubIsCategory .⨟-idₗ   = Sub-⨟-idₗ

instance
  TmRenIsPresheaf : IsPresheaf Tm
  TmRenIsPresheaf ._⟨_⟩ t ρ   = rename ρ t
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

------------------------------------------------------------------------------
-- Trivial proofs

var≢op : {x : Fin Θ} {i : D .Op} {ts : Tm Θ ^ D .rules i}
  → op (i , ts) ≢ ` x
var≢op ()

op≢var : {x : Fin Θ} {i : D .Op} {ts : Tm Θ ^ D .rules i}
  → ` x ≢ op (i , ts)
op≢var()

op-inj
  : {(i , ts) (j , us) : ⟦ D ⟧ (Tm Ξ)}
  → _≡_ {A = Tm _ } (op (i , ts)) (op (j , us))
  → Σ (i ≡ j) λ where refl → ts ≡ us
  -- Σ (l ≡ k) λ where refl → Σ (i ≡ j) λ where refl → ts ≡ us
op-inj refl = refl , refl

op-inj₁₂
  : {(i , ts) (j , us) : ⟦ D ⟧ (Tm Ξ)}
  → _≡_ {A = Tm _ } (op (i , ts)) (op (j , us))
  → i ≡ j -- (l , i) ≡ (k , j)
op-inj₁₂ refl = refl

op-inj₃
  : {i : D .Op} {ts us : Tm Ξ ^ D .rules i}
  → _≡_ {A = Tm Ξ} (op (i , ts)) (op (i , us))
  → ts ≡ us
op-inj₃ refl = refl -- refl

op-cong⇔ : {i : D .Op} 
  → {ts us : (Tm Ξ) ^ (D .rules i)}
  → ts ≡ us ⇔ _≡_ {A = Tm Ξ} (op (i , ts)) (op (i , us))
op-cong⇔ {i = i} = record
  { to   = cong λ ts → op (i , ts)
  ; from = op-inj₃ }

------------------------------------------------------------------------------
-- Proofs about free variables

mutual
  ∈ᵥ→∈fv : x ∈ᵥ t → x ∈ fv t
  ∈ᵥ→∈fv (here p) = here p
  ∈ᵥ→∈fv (op   p) = ∈ᵥ→∈fvⁿ p

  ∈ᵥ→∈fvⁿ : x ∈ᵥₛ ts → x ∈ fvⁿ ts
  ∈ᵥ→∈fvⁿ (head x∈)         = ∈-++⁺ˡ        (∈ᵥ→∈fv x∈)
  ∈ᵥ→∈fvⁿ (tail {_} {t} x∈) = ∈-++⁺ʳ (fv t) (∈ᵥ→∈fvⁿ x∈)

module _ {Ξ : ℕ} where mutual 
  ∈fv→∈ᵥ : {t : Tm Ξ} {x : Fin Ξ} → x ∈ fv t → x ∈ᵥ t
  ∈fv→∈ᵥ {` x}  (here px) = here px
  ∈fv→∈ᵥ {op _} x∈        = op (∈fv→∈ᵥⁿ x∈)

  ∈fv→∈ᵥⁿ : {x : Fin Ξ} {ts : Tm Ξ ^ n} → x ∈ fvⁿ ts → x ∈ᵥₛ ts
  ∈fv→∈ᵥⁿ  {suc l} {x} {ts = t ∷ ts} x∈ with ∈-++⁻ (fv t) x∈
  ... | inl x∈t  = head (∈fv→∈ᵥ x∈t)
  ... | inr x∈ts = tail (∈fv→∈ᵥⁿ x∈ts)

module _ {Ξ : ℕ} where
  Any∈ᵥ→Any∈ : {ts : Tms Ξ} {i : Fin Ξ}
    → L.Any (_∈ᵥ_ i) ts → L.Any (_≡_ i) (fvs ts)
  Any∈ᵥ→Any∈ {t ∷ ts} (here px) = L.++⁺ˡ (∈ᵥ→∈fv px)
  Any∈ᵥ→Any∈ {t ∷ ts} (there x) = L.++⁺ʳ (fv t) (Any∈ᵥ→Any∈ x)

  Any∈→Any∈ᵥ : {ts : Tms Ξ} {i : Fin Ξ}
    → L.Any (_≡_ i) (fvs ts) → L.Any (_∈ᵥ_ i) ts
  Any∈→Any∈ᵥ {t ∷ ts} x∈ with L.++⁻ (fv t) x∈
  ... | inl x∈t  = here (∈fv→∈ᵥ x∈t)
  ... | inr x∈ts = there (Any∈→Any∈ᵥ x∈ts)

∈sub-++ : {xs ys : Fins Ξ}
  → (ρ : Sub⊆ xs Θ) (σ : Sub⊆ ys Θ)
  → Consistent ρ σ
  → Sub⊆ (xs ++ ys) Θ
∈sub-++ {Ξ} {Θ} {xs} {ys} (ρ , p) (σ , q) con = γ , conγ
  where
    γ : (i : Fin Ξ) → i ∈ (xs ++ ys) → Tm Θ
    γ i i∈ with L.++⁻ xs i∈
    ... | inl x = ρ _ x
    ... | inr y = σ _ y

    conγ : ∀ {i} → (x y : i ∈ (xs ++ ys)) → γ i x ≡ γ i y
    conγ x y with L.++⁻ xs x | L.++⁻ xs y
    ... | inl x₁ | inl x₂ = p x₁ x₂
    ... | inl x₁ | inr y₁ = con x₁ y₁
    ... | inr y₁ | inl x₁ = sym (con x₁ y₁)
    ... | inr y₁ | inr y₂ = q y₁ y₂

module _ {σ₁ σ₂ : Sub Θ₁ Θ₂} where mutual
  ≡-fv-inv : (A : Tm Θ₁) 
    → A ⟨ σ₁ ⟩ ≡ A ⟨ σ₂ ⟩
    → x ∈ᵥ A
    → σ₁ x ≡ σ₂ x -- lookup σ₁ x ≡ lookup σ₂ x
  ≡-fv-inv (` x)      p (here refl) = p
  ≡-fv-inv (op (i , ts)) p (op x∈)    = ≡-fv-invⁿ ts (op-inj₃ p) x∈

  ≡-fv-invⁿ : (As : Tm Θ₁ ^ n)
    → subⁿ σ₁ As ≡ subⁿ σ₂ As
    → x ∈ᵥₛ As
    → σ₁ x ≡ σ₂ x -- lookup σ₁ x ≡ lookup σ₂ x
  ≡-fv-invⁿ (A ∷ As) p (head x∈) = ≡-fv-inv  A  (V.∷-injectiveˡ p) x∈
  ≡-fv-invⁿ (A ∷ As) p (tail x∈) = ≡-fv-invⁿ As (V.∷-injectiveʳ p) x∈

module _ {σ₁ σ₂ : Sub Θ₁ Θ₂} where mutual
  ≡-fv : (A : Tm Θ₁)
    → (∀ {x} → x ∈ᵥ A → σ₁ x ≡ σ₂ x)
    → A ⟨ σ₁ ⟩ ≡ A ⟨ σ₂ ⟩
  ≡-fv (` x)         p = p (here refl)
  ≡-fv (op (_ , ts)) p = cong (λ ts → op (_ , ts)) (≡-fvⁿ ts (p ∘ op)) -- (≡-fvⁿ ts p)

  ≡-fvⁿ : {n : ℕ} (As : Tm Θ₁ ^ n)
    → (∀ {x} → x ∈ᵥₛ As → σ₁ x ≡ σ₂ x) -- lookup σ₁ x ≡ lookup σ₂ x)
    → subⁿ σ₁ As ≡ subⁿ σ₂ As

  ≡-fvⁿ {zero}  []       _ = refl
  ≡-fvⁿ {suc n} (A ∷ As) p = cong₂ _∷_
    (≡-fv A (p ∘ head)) (≡-fvⁿ As (p ∘ tail))

------------------------------------------------------------------------------
-- Renames are also substitutions

module _ {ρ : Fin Θ₁ → Fin Θ₁} where mutual
  rename-is-sub
    : (t : Tm Θ₁)
    → t ⟨ `_ ∘ ρ ⟩ ≡ t ⟨ ρ ⟩
  rename-is-sub (` x)      = refl -- lookup∘tabulate _ x
  rename-is-sub (op (i , ts)) = cong (op ∘ (i ,_)) (rename-is-subⁿ ts)

  rename-is-subⁿ
    : (ts : Tm Θ₁ ^ n)
    → ts ⟨ `_ ∘ ρ ⟩ ≡ ts ⟨ ρ ⟩
  rename-is-subⁿ []       = refl
  rename-is-subⁿ (t ∷ ts) = cong₂ _∷_ (rename-is-sub t) (rename-is-subⁿ ts)
