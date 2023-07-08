open import Syntax.Simple.Description

module Syntax.Simple.Properties (D : Desc) where

open import Prelude
  hiding (_+_)

open import Syntax.Simple.Term        D

open N using (_+_)

open ≡-Reasoning

private variable
  Ξ Θ Θ₁ Θ₂ Θ₃ n : ℕ
  ts us   : Tm Θ ^ n
  σ₁ σ₂   : Sub Ξ Θ
  xs ys   : Fins# Ξ
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

------------------------------------------------------------------------------
-- Proofs about free variables

mutual
  ∈ᵥ→∈vars : x ∈ᵥ t → x #∈ vars t
  ∈ᵥ→∈vars (here eq) = here eq
  ∈ᵥ→∈vars (op  x∈) = ∈ᵥₛ→∈varsⁿ x∈

  ∈ᵥₛ→∈varsⁿ : x ∈ᵥₛ ts → x #∈ varsⁿ ts
  ∈ᵥₛ→∈varsⁿ (head x∈) = ∪⁺ˡ (∈ᵥ→∈vars x∈)
  ∈ᵥₛ→∈varsⁿ (tail {_} {t} x∈) = ∪⁺ʳ (vars t) (∈ᵥₛ→∈varsⁿ x∈)

mutual
  ∈vars→∈ᵥ : x #∈ vars t → x ∈ᵥ t
  ∈vars→∈ᵥ {t = ` x} (here px) = here px
  ∈vars→∈ᵥ {t = op x} x∈ = op (∈varsⁿ→∈ᵥₛ x∈)

  ∈varsⁿ→∈ᵥₛ : x #∈ varsⁿ ts → x ∈ᵥₛ ts
  ∈varsⁿ→∈ᵥₛ {ts = t ∷ ts} x∈ with ∈-∪⁻ (vars t) x∈
  ... | inl x∈t  = head (∈vars→∈ᵥ x∈t)
  ... | inr x∈ts = tail (∈varsⁿ→∈ᵥₛ x∈ts)


module _ {σ₁ σ₂ : Sub Θ₁ Θ₂} where mutual
  ≡-fv-inv : (A : Tm Θ₁)
    → A ⟨ σ₁ ⟩ ≡ A ⟨ σ₂ ⟩
    → x ∈ᵥ A
    → σ₁ x ≡ σ₂ x
  ≡-fv-inv (` x)      p (here refl) = p
  ≡-fv-inv (op (i , ts)) p (op x∈)    = ≡-fv-invⁿ ts (op-inj₃ p) x∈

  ≡-fv-invⁿ : (As : Tm Θ₁ ^ n)
    → subⁿ σ₁ As ≡ subⁿ σ₂ As
    → x ∈ᵥₛ As
    → σ₁ x ≡ σ₂ x
  ≡-fv-invⁿ (A ∷ As) p (head x∈) = ≡-fv-inv  A  (V.∷-injectiveˡ p) x∈
  ≡-fv-invⁿ (A ∷ As) p (tail x∈) = ≡-fv-invⁿ As (V.∷-injectiveʳ p) x∈

module _ {σ₁ σ₂ : Sub Θ₁ Θ₂} where mutual
  ≡-fv : (A : Tm Θ₁)
    → (∀ {x} → x ∈ᵥ A → σ₁ x ≡ σ₂ x)
    → A ⟨ σ₁ ⟩ ≡ A ⟨ σ₂ ⟩
  ≡-fv (` x)         p = p (here refl)
  ≡-fv (op (_ , ts)) p = cong (λ ts → op (_ , ts)) (≡-fvⁿ ts (p ∘ op))

  ≡-fvⁿ : {n : ℕ} (As : Tm Θ₁ ^ n)
    → (∀ {x} → x ∈ᵥₛ As → σ₁ x ≡ σ₂ x)
    → subⁿ σ₁ As ≡ subⁿ σ₂ As

  ≡-fvⁿ {zero}  []       _ = refl
  ≡-fvⁿ {suc n} (A ∷ As) p = cong₂ _∷_
    (≡-fv A (p ∘ head)) (≡-fvⁿ As (p ∘ tail))

------------------------------------------------------------------------
-- Properties regarding Partial Substitution

∅≤ρ : {ρ : ∃Sub⊆ Ξ} → empty ≤ ρ
∅≤ρ = record
  { domain-ext  = λ ()
  ; consistency = λ ()
  }
-- ≤ is a preorder
≤-refl : (ρ : ∃Sub⊆ Ξ) → ρ ≤ ρ
≤-refl ρ = record
  { domain-ext  = λ x → x
  ; consistency = λ _ → refl
  }

≤-trans : {ρ σ γ : ∃Sub⊆ Ξ}
  → ρ ≤ σ → σ ≤ γ → ρ ≤ γ
≤-trans {_} {xs , ρ} {ys , σ} {zs , γ} (≤-con xs⊆ys con₁) (≤-con ys⊆zs con₂) = record
  { domain-ext  = ⊆-trans xs⊆ys ys⊆zs
  ; consistency = λ x∈ → begin
    ρ x∈
      ≡⟨ con₁ _ ⟩
    σ (xs⊆ys x∈)
      ≡⟨ con₂ _ ⟩
    γ (ys⊆zs (xs⊆ys x∈))
      ∎
  }

-- Partial substitutions vars t ⊆ xs is supposed to be a proposition
-- (but it cannot be proved in vanilla Agda)

module _ (ρ : Sub⊆ Ξ xs) where
  mutual
    sub⊆-⊆-irrelevant : (t : Tm Ξ) (t⊆ t⊆′ : vars t #⊆ xs)
      → sub⊆ ρ t t⊆ ≡ sub⊆ ρ t t⊆′
    sub⊆-⊆-irrelevant (` x)         t⊆ t⊆′ = cong ρ (#∈-uniq _ _)
    sub⊆-⊆-irrelevant (op (i , ts)) t⊆ t⊆′ =
      cong (λ ts → op (i , ts)) (sub⊆ⁿ-⊆-irrelevant ts _ _)

    sub⊆ⁿ-⊆-irrelevant : (ts : Tm Ξ ^ n) (t⊆ t⊆′ : varsⁿ ts #⊆ xs)
      → sub⊆ⁿ ρ ts t⊆ ≡ sub⊆ⁿ ρ ts t⊆′
    sub⊆ⁿ-⊆-irrelevant []       t⊆ t⊆′ = refl
    sub⊆ⁿ-⊆-irrelevant (t ∷ ts) t⊆ t⊆′ = cong₂ _∷_
      (sub⊆-⊆-irrelevant t _ _) (sub⊆ⁿ-⊆-irrelevant ts _ _)

mutual
  ρ=σ→subρ=subσ : (t : Tm Ξ) (ρ : Sub⊆ Ξ xs) (σ : Sub⊆ Ξ ys)
    → (⊆xs : vars t #⊆ xs) (⊆ys : vars t #⊆ ys)
    → (∀ {x} (x∈ : x #∈ vars t) → ρ (⊆xs x∈) ≡ σ (⊆ys x∈))
    → sub⊆ ρ t ⊆xs ≡ sub⊆ σ t ⊆ys
  ρ=σ→subρ=subσ (` x)  ρ σ ⊆xs ⊆ys ρ=σ = ρ=σ (here refl)
  ρ=σ→subρ=subσ (op (i , ts)) ρ σ ⊆xs ⊆ys ρ=σ =
    cong (λ ts → op (i , ts)) (ρ=σ→subρ=subσⁿ ts ρ σ ⊆xs ⊆ys ρ=σ)

  ρ=σ→subρ=subσⁿ : (ts : Tm Ξ ^ n) (ρ : Sub⊆ Ξ xs) (σ : Sub⊆ Ξ ys)
    → (⊆xs : varsⁿ ts #⊆ xs) (⊆ys : varsⁿ ts #⊆ ys)
    → (∀ {x} (x∈ : x #∈ varsⁿ ts) → ρ (⊆xs x∈) ≡ σ (⊆ys x∈))
    → sub⊆ⁿ ρ ts ⊆xs ≡ sub⊆ⁿ σ ts ⊆ys
  ρ=σ→subρ=subσⁿ []       ρ σ ⊆xs ⊆ys ρ=σ = refl
  ρ=σ→subρ=subσⁿ (t ∷ ts) ρ σ ⊆xs ⊆ys ρ=σ = cong₂ _∷_
    (ρ=σ→subρ=subσ  t  ρ σ (∪-⊆⁻ˡ ⊆xs)          (∪-⊆⁻ˡ ⊆ys)          (λ x∈ → ρ=σ (∪⁺ˡ x∈)))
    (ρ=σ→subρ=subσⁿ ts ρ σ (∪-⊆⁻ʳ (vars t) ⊆xs) (∪-⊆⁻ʳ (vars t) ⊆ys) λ x∈ → ρ=σ (∪⁺ʳ (vars t) x∈))

------------------------------------------------------------------------
-- Substitution ⇒ Partial substitution
x≠y→sucx≠sucy
  : {x y : Fin Ξ}
  → x ≢ y → suc x ≢ suc y
x≠y→sucx≠sucy neq = neq ∘ F.suc-injective

0#suc : (xs : Fins# Ξ)
  → zero # map suc x≠y→sucx≠sucy xs
0#suc []            = tt
0#suc (cons a xs x) = F.0≢1+n , 0#suc xs

enumerate : (Ξ : ℕ) → List# (Fin Ξ)
enumerate zero    = []
enumerate (suc i) =
  cons zero (map suc x≠y→sucx≠sucy  (enumerate i)) (0#suc (enumerate i))

x∈xs→1+x∈1+xs
  : x #∈ xs
  → suc x #∈ map suc x≠y→sucx≠sucy xs
x∈xs→1+x∈1+xs (here eq)  = here (cong suc eq)
x∈xs→1+x∈1+xs (there x∈) = there (x∈xs→1+x∈1+xs x∈)

Sub⇒Sub⊆ : Sub Ξ 0 → Sub⊆ Ξ (enumerate Ξ)
Sub⇒Sub⊆ ρ {x} x∈ = ρ x

⊆enum : (x : Fin Ξ) → x #∈ enumerate Ξ
⊆enum zero    = here refl
⊆enum (suc x) = there (x∈xs→1+x∈1+xs (⊆enum x))

t⊆Ξ : (t : Tm Ξ) → vars t #⊆ enumerate Ξ
t⊆Ξ t {x} x∈ = ⊆enum x

mutual
  Sub⇒Sub⊆-=
    : (σ : Sub Ξ 0)
    → (t : Tm Ξ)
    → sub⊆ (Sub⇒Sub⊆ σ) t (t⊆Ξ t) ≡ sub σ t
  Sub⇒Sub⊆-= σ (` x)         = refl
  Sub⇒Sub⊆-= σ (op (i , ts)) =
    cong (λ ts → op (i , ts)) (Sub⇒Sub⊆-=ⁿ σ ts)

  Sub⇒Sub⊆-=ⁿ
    : (σ : Sub Ξ 0)
    → (t : Tm Ξ ^ n)
    → sub⊆ⁿ (Sub⇒Sub⊆ σ) t (λ {x} _ → ⊆enum x) ≡ subⁿ σ t
  Sub⇒Sub⊆-=ⁿ σ []       = refl
  Sub⇒Sub⊆-=ⁿ σ (t ∷ ts) = cong₂ _∷_ (Sub⇒Sub⊆-= σ t) (Sub⇒Sub⊆-=ⁿ σ ts)

------------------------------------------------------------------------
-- Partial Substitution to Substitution
Sub⊆⇒Sub
  : Sub⊆ Ξ xs → ((x : Fin Ξ) → x #∈ xs)
  → Sub Ξ 0
Sub⊆⇒Sub σ ∀x∈xs x = σ (∀x∈xs x)

module _ (ρ : Sub⊆ Ξ xs) (∀x∈xs : (x : Fin Ξ) → x #∈ xs) where mutual
  Sub⊆⇒Sub-≡
    : (t : Tm Ξ)
    → sub (Sub⊆⇒Sub ρ ∀x∈xs) t ≡ sub⊆ ρ t (λ {x} _ → ∀x∈xs x)
  Sub⊆⇒Sub-≡ (` x)         = refl
  Sub⊆⇒Sub-≡ (op (i , ts)) = cong (λ ts → op (i , ts)) (Sub⊆⇒Sub-≡ⁿ ts)

  Sub⊆⇒Sub-≡ⁿ
    : (ts : Tm Ξ ^ n)
    → subⁿ ((Sub⊆⇒Sub ρ ∀x∈xs)) ts ≡ sub⊆ⁿ ρ ts λ {x} _ → ∀x∈xs x
  Sub⊆⇒Sub-≡ⁿ []       = refl
  Sub⊆⇒Sub-≡ⁿ (t ∷ ts) = cong₂ _∷_ (Sub⊆⇒Sub-≡ t) (Sub⊆⇒Sub-≡ⁿ ts)

------------------------------------------------------------------------
--

module _ (σ : Sub Ξ 0) (ρ : Sub⊆ Ξ xs) where
  mutual
    σ=ρ|A
      : (t : Tm Ξ) (t⊆ : vars t #⊆ xs)
      → sub σ t ≡ sub⊆ ρ t t⊆
      → ∀ {x} (x∈ : x #∈ vars t)
      → ρ (t⊆ x∈) ≡ σ x
    σ=ρ|A (` x)         t⊆ eq (here refl) = sym eq
    σ=ρ|A (op (i , ts)) t⊆ eq {y} y∈ = σ=ρ|Aⁿ ts t⊆ (op-inj₃ eq) y∈

    σ=ρ|Aⁿ
      : (ts : Tm Ξ ^ n) (ts⊆ : varsⁿ ts #⊆ xs)
      → subⁿ σ ts ≡ sub⊆ⁿ ρ ts ts⊆
      → ∀ {x} (x∈ : x #∈ varsⁿ ts)
      → ρ (ts⊆ x∈) ≡ σ x
    σ=ρ|Aⁿ (t ∷ ts) ts⊆ eq x∈ with ∈-∪⁻ (vars t) x∈
    ... | inl x∈t  = trans (cong ρ (#∈-uniq _ _)) (σ=ρ|A t (∪-⊆⁻ˡ ts⊆) (V.∷-injectiveˡ eq) x∈t)
    ... | inr x∈ts = trans (cong ρ (#∈-uniq _ _)) (σ=ρ|Aⁿ ts (∪-⊆⁻ʳ (vars t) ts⊆) (V.∷-injectiveʳ eq) x∈ts)

------------------------------------------------------------------------
-- Constructions regarding partial substitution properties

open Equivalence
Pρ→MinExtP : {P : Sub⊆-Prop Ξ} {ρ : ∃Sub⊆ Ξ} → P ρ → Min (Ext ρ P) ρ
Pρ→MinExtP {Ξ} {P} {ρ} Pρ = min-con (ext-con (≤-refl ρ) Pρ) λ σ (ext-con ρ≤σ _) → ρ≤σ

Ext⇔ : {P Q : Sub⊆-Prop Ξ}
  → ((ρ : ∃Sub⊆ Ξ) → P ρ ⇔ Q ρ)
  → (ρ σ : ∃Sub⊆ Ξ) → Ext ρ P σ ⇔ Ext ρ Q σ
Ext⇔ P⇔Q ρ σ = record
  { to   = λ (ext-con ρ≤σ Pσ) → ext-con ρ≤σ (P⇔Q σ .to Pσ)
  ; from = λ (ext-con ρ≤σ Qσ) → ext-con ρ≤σ (P⇔Q σ .from Qσ)
  }

Min⇔ : {P Q : Sub⊆-Prop Ξ}
  → (∀ ρ → P ρ ⇔ Q ρ)
  → ∀ ρ → Min P ρ ⇔ Min Q ρ
Min⇔ P⇔Q ρ = record
  { to   = λ (min-con Pρ minρ) →
    min-con (P⇔Q ρ .to Pρ)   λ σ Qσ → minρ σ (P⇔Q σ .from Qσ)
  ; from = λ (min-con Qρ minρ) →
    min-con (P⇔Q ρ .from Qρ) λ σ Pσ → minρ σ (P⇔Q σ .to Pσ)
  }

MinDec⇔ : {P Q : Sub⊆-Prop Ξ}
  → (∀ ρ → P ρ ⇔ Q ρ)
  → MinDec P ⇔ MinDec Q
MinDec⇔ P⇔Q = record
  { to   = λ where
    (yesₘ ρ Minρ) → yesₘ ρ (Min⇔ P⇔Q ρ .to Minρ)
    (noₘ ¬Pσ)     → noₘ (λ σ Qσ → ¬Pσ σ (P⇔Q σ .from Qσ))
  ; from = λ where
    (yesₘ ρ Minρ) → yesₘ ρ (Min⇔ P⇔Q ρ .from Minρ)
    (noₘ ¬Qσ)     → noₘ λ σ Pσ → ¬Qσ σ (P⇔Q σ .to Pσ)
  }

MinDecExt∅⇔MinDec
  : {P : Sub⊆-Prop Ξ}
  → MinDec (Ext empty P) ⇔ MinDec P
MinDecExt∅⇔MinDec = MinDec⇔ λ ρ → record
  { to   = λ where
    (ext-con _ Pρ) → Pρ
  ; from = λ Pρ → ext-con ∅≤ρ Pρ
  }

optimist
  : {P Q : Sub⊆-Prop Ξ}
  → (ρ ρ̅₁ ρ̅₂ : ∃Sub⊆ Ξ)
  → ↑-closed P → Min (Ext ρ P) ρ̅₁ → Min (Ext ρ̅₁ Q) ρ̅₂
  → Min (Ext ρ (P ∧ Q)) ρ̅₂
optimist ρ ρ̅ ρ̅₂ ↑P (min-con (ext-con ρ≤ρ̅ Pρ̅) minρ) (min-con (ext-con ρ̅≤ρ̅₂ Qρ̅) minρ₂) = record
  { proof      = record
    { ext     = ≤-trans ρ≤ρ̅ ρ̅≤ρ̅₂
    ; witness = (↑P ρ̅≤ρ̅₂ Pρ̅) , Qρ̅
    }
  ; minimality = λ where
    σ (ext-con ρ≤σ (Pσ , Qσ)) → minρ₂ σ
      (ext-con (minρ σ (ext-con ρ≤σ Pσ)) Qσ)
  }

failure-propagate : {P Q : Sub⊆-Prop Ξ} → (ρ ρ̅ : ∃Sub⊆ Ξ)
  → Min (Ext ρ P) ρ̅
  → (∀ σ → ¬ Ext ρ̅ Q σ)
  → ∀ σ → ¬ Ext ρ (P ∧ Q) σ
failure-propagate ρ ρ̅ (min-con Pρ̅ minρ̅) ¬Q σ (ext-con ρ≤σ (Pσ , Qσ)) =
  ¬Q σ (ext-con (minρ̅ σ (ext-con ρ≤σ Pσ)) Qσ)

↑≈ : (t : Tm Ξ) (u : Tm 0) → ↑-closed (t ≈ u)
↑≈ t u {xs , ρ} {ys , σ} (≤-con xs⊆ys con) (t⊆xs , eq) =
  ⊆-trans t⊆xs xs⊆ys , (begin
    sub⊆ σ t _
      ≡⟨ ρ=σ→subρ=subσ t σ ρ
        (⊆-trans t⊆xs xs⊆ys) t⊆xs (λ x∈ → sym (con (t⊆xs x∈))) ⟩
    sub⊆ ρ t t⊆xs
      ≡⟨ eq ⟩
    u
      ∎)

↑≈ⁿ : (ts : Tm Ξ ^ n) (us : Tm 0 ^ n) → ↑-closed (ts ≈ⁿ us)
↑≈ⁿ ts us {xs , ρ} {ys , σ} (≤-con xs⊆ys con) (t⊆xs , eq) =
  (⊆-trans t⊆xs xs⊆ys) , (begin
  sub⊆ⁿ σ ts _
    ≡⟨ ρ=σ→subρ=subσⁿ ts σ ρ
        (⊆-trans t⊆xs xs⊆ys) t⊆xs (λ x∈ → sym (con (t⊆xs x∈))) ⟩
  sub⊆ⁿ ρ ts t⊆xs
    ≡⟨ eq ⟩
  us
    ∎)

-- Simple facts about unification
ts≈us⇔opts≈opus
  : ∀ {i} (ts : Tm Ξ ^ D .rules i) (us : Tm 0 ^ D .rules i)
  → (ρ : ∃Sub⊆ Ξ)
  → (ts ≈ⁿ us) ρ ⇔ (op (i , ts) ≈ op (i , us)) ρ
ts≈us⇔opts≈opus {_} {i} ts us ρ = record
  { to   = λ (ts⊆xs , ts=us) → ts⊆xs , cong op (cong (i ,_) ts=us)
  ; from = λ (t⊆xs  , t=u)   → t⊆xs  , op-inj₃ t=u
  }

t≈u×ts≈us⇔tts≈uus
  : (t : Tm Ξ) (u : Tm 0) (ts : Tm Ξ ^ n) (us : Tm 0 ^ n)
  → (ρ : ∃Sub⊆ Ξ)
  → ((ts ≈ⁿ us) ∧ (t ≈ u)) ρ ⇔ (t ∷ ts ≈ⁿ u ∷ us) ρ
t≈u×ts≈us⇔tts≈uus t u ts us ρ@(xs , ρf) = record
  { to   = helper₁
  ; from = helper₂ }
  where
    helper₁ : (ts ≈ⁿ us ∧ t ≈ u) ρ → (t ∷ ts ≈ⁿ u ∷ us) ρ
    helper₁ ((ts⊆ , ts≈us) , (t⊆ , t≈u)) = (∪-⊆⁺ t⊆ ts⊆) , cong₂ _∷_
      (begin
        sub⊆ ρf t _
          ≡⟨ sub⊆-⊆-irrelevant ρf t _ _ ⟩
        sub⊆ ρf t t⊆
          ≡⟨ t≈u ⟩
        u ∎ )

      (begin
        sub⊆ⁿ ρf ts _
          ≡⟨ sub⊆ⁿ-⊆-irrelevant ρf ts _ _ ⟩
        sub⊆ⁿ ρf ts _
          ≡⟨ ts≈us ⟩
        us ∎)

    helper₂ : (t ∷ ts ≈ⁿ u ∷ us) ρ → (ts ≈ⁿ us ∧ t ≈ u) ρ
    helper₂ (ts⊆ , tts≈uus) = let t≈u , ts≈us = V.∷-injective tts≈uus  in
      ((∪-⊆⁻ʳ (vars t) ts⊆) , (begin
        sub⊆ⁿ ρf ts _
          ≡⟨ sub⊆ⁿ-⊆-irrelevant ρf ts _ _ ⟩
        sub⊆ⁿ ρf ts _
          ≡⟨ ts≈us ⟩
        us
          ∎)) ,
      ∪-⊆⁻ˡ ts⊆ , (begin
        sub⊆ ρf t _
          ≡⟨ sub⊆-⊆-irrelevant ρf t _ _ ⟩
        sub⊆ ρf t _
          ≡⟨ t≈u ⟩
        u
          ∎)

⊆→Sub⊆
  : ys #⊆ xs → Sub⊆ Ξ xs
  → Sub⊆ Ξ ys
⊆→Sub⊆ ys⊆xs ρ = ρ ∘ ys⊆xs

module _ (ρ : Sub⊆ Ξ xs) (σ : Sub⊆ Ξ ys) where mutual
  sub⊆-cong
    : (t : Tm Ξ) (t⊆xs : vars t #⊆ xs)  (t⊆ys : vars t #⊆ ys)
    → (∀ {x} (x∈ : x #∈ vars t) → ρ (t⊆xs x∈) ≡ σ (t⊆ys x∈))
    → sub⊆ ρ t t⊆xs ≡ sub⊆ σ t t⊆ys
  sub⊆-cong (` x)         t⊆xs t⊆ys eq = eq (here refl)
  sub⊆-cong (op (i , ts)) t⊆xs t⊆ys eq = cong (λ ts → op (i , ts))
    (sub⊆-congⁿ ts _ _ eq)

  sub⊆-congⁿ
    : (ts : Tm Ξ ^ n) (⊆xs : varsⁿ ts #⊆ xs)  (⊆ys : varsⁿ ts #⊆ ys)
    → (∀ {x} (x∈ : x #∈ varsⁿ ts) → ρ (⊆xs x∈) ≡ σ (⊆ys x∈))
    → sub⊆ⁿ ρ ts ⊆xs ≡ sub⊆ⁿ σ ts ⊆ys
  sub⊆-congⁿ []       ⊆xs ⊆ys eq = refl
  sub⊆-congⁿ (t ∷ ts) ⊆xs ⊆ys eq = cong₂ _∷_
    (sub⊆-cong t _ _ (eq ∘ ∪⁺ˡ)) (sub⊆-congⁿ ts _ _ (eq ∘ ∪⁺ʳ (vars t)))

module _ (σ : Sub Ξ 0) where mutual
  sub⊆=sub
    : (t : Tm Ξ)
    → sub σ t ≡ sub⊆ (Sub⇒Sub⊆ σ) t λ {x} _ → ⊆enum x
  sub⊆=sub (` x)         = refl
  sub⊆=sub (op (i , ts)) =
    cong (λ ts → op (i , ts)) (sub⊆=subⁿ ts)

  sub⊆=subⁿ
    : (ts : Tm Ξ ^ n)
    → subⁿ σ ts ≡ sub⊆ⁿ (Sub⇒Sub⊆ σ) ts λ {x} _ → ⊆enum x
  sub⊆=subⁿ []       = refl
  sub⊆=subⁿ (t ∷ ts) = cong₂ _∷_ (sub⊆=sub t) (sub⊆=subⁿ ts)

module _ (ρ : Sub⊆ Ξ xs) (⊆xs : ∀ x → x #∈ xs) where mutual
  sub⊆=sub′
    : (t : Tm Ξ) (t⊆ : vars t #⊆ xs)
    → sub (ρ ∘ ⊆xs) t ≡ sub⊆ ρ t t⊆
  sub⊆=sub′ (` x)         t⊆ = cong ρ (#∈-uniq _ _) -- refl
  sub⊆=sub′ (op (i , ts)) t⊆ =
    cong (λ ts → op (i , ts)) (sub⊆=subⁿ′ ts _)

  sub⊆=subⁿ′
    : (ts : Tm Ξ ^ n) (ts⊆ : varsⁿ ts #⊆ xs)
    → subⁿ (ρ ∘ ⊆xs) ts ≡ sub⊆ⁿ ρ ts ts⊆
  sub⊆=subⁿ′ []       ts⊆ = refl
  sub⊆=subⁿ′ (t ∷ ts) ts⊆ = cong₂ _∷_
   (sub⊆=sub′ t _) (sub⊆=subⁿ′ ts _)

domain-cmp : (t : Tm Ξ) (u : Tm 0)
  → (xs : Fins# Ξ) (ρ : Sub⊆ Ξ xs)
  → Min (t ≈ u) (xs , ρ)
  → xs #⊆ vars t
domain-cmp {Ξ} t u xs ρ (min-con (t⊆xs , eq) minσ) x∈ =
  minσ (_ , ⊆→Sub⊆ t⊆xs ρ) ((λ y∈ → y∈) ,
    (begin
      sub⊆ (⊆→Sub⊆ t⊆xs ρ) t (λ y∈ → y∈)
        ≡⟨ sub⊆-cong (ρ ∘ t⊆xs) ρ t _ t⊆xs (λ _ → refl) ⟩
      sub⊆ ρ t t⊆xs
        ≡⟨ eq ⟩
      u ∎)) .domain-ext x∈

module _ (ρ : Sub⊆ Ξ xs) (σ : Sub Ξ 0) where mutual
  sub-σ=sub⊆-ρ→σ=ρ
    : (t : Tm Ξ) (t⊆ : vars t #⊆ xs)
    → sub⊆ ρ t t⊆ ≡ sub σ t
    → ∀ {x} (x∈ : x #∈ vars t)
    → ρ (t⊆ x∈) ≡ σ x
  sub-σ=sub⊆-ρ→σ=ρ (` x)         t⊆ eq (here refl) = eq
  sub-σ=sub⊆-ρ→σ=ρ (op (i , ts)) t⊆ eq y∈ =
    sub-σ=sub⊆-ρ→σ=ρⁿ ts t⊆ (op-inj₃ eq) y∈

  sub-σ=sub⊆-ρ→σ=ρⁿ
    : (ts : Tm Ξ ^ n) (⊆xs : varsⁿ ts #⊆ xs)
    → sub⊆ⁿ ρ ts ⊆xs ≡ subⁿ σ ts
    → ∀ {x} (x∈ : x #∈ varsⁿ ts)
    → ρ (⊆xs x∈) ≡ σ x
  sub-σ=sub⊆-ρ→σ=ρⁿ (t ∷ ts) ⊆xs eq {x} x∈ with ∈-∪⁻ (vars t) x∈
  ... | inl ∈t  = begin
    ρ (⊆xs x∈)
      ≡⟨ cong ρ (#∈-uniq _ _) ⟩
    ρ _
      ≡⟨ sub-σ=sub⊆-ρ→σ=ρ t _ (V.∷-injectiveˡ eq) ∈t ⟩
    σ x
      ∎
  ... | inr ∈ts = begin
    ρ (⊆xs x∈)
      ≡⟨ cong ρ (#∈-uniq _ _) ⟩
    ρ _
      ≡⟨ sub-σ=sub⊆-ρ→σ=ρⁿ ts _ (V.∷-injectiveʳ eq) ∈ts ⟩
    σ x ∎
