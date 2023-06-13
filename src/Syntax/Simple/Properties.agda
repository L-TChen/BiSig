{-# OPTIONS --safe #-}

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
{- tabulate-cong (λ i → begin
  sub γ (sub (Sub-⨟ σ ρ) (` i)) 
    ≡⟨ cong (sub γ ) (sub-⨟ σ ρ (` i)) ⟩
  sub γ (sub ρ (sub σ (` i)))
    ≡⟨ sym $ sub-⨟ ρ γ (sub σ $ ` i) ⟩
  sub (Sub-⨟ ρ γ) (sub σ (` i))
    ∎)
-}

Sub-⨟-idᵣ : (σ : Sub Θ n)
  → (i : Fin Θ)
  → Sub-⨟ σ Sub-id i ≡ σ i
Sub-⨟-idᵣ σ i = sub-id (σ i)
{- begin
  Sub-⨟ σ Sub-id
    ≡⟨ tabulate-cong (λ i → sub-id (lookup σ i)) ⟩
  tabulate (λ i → lookup σ i) 
    ≡⟨ tabulate∘lookup σ ⟩
  σ
    ∎
-}


Sub-⨟-idₗ : (σ : Sub Θ n)
  → (i : Fin Θ)
  → Sub-⨟ Sub-id σ i ≡ σ i
Sub-⨟-idₗ σ i = refl
{- begin
  Sub-⨟ Sub-id σ
    ≡⟨ tabulate-cong (λ i → cong (sub σ) (sub-id (` i))) ⟩
  tabulate (λ i → sub σ (` i))
    ≡⟨ tabulate∘lookup σ ⟩
  σ
    ∎
-}

instance
  RenIsCategory : IsCategory ℕ Ren _≡_
  RenIsCategory .isEquivalence = ≡-isEquivalence
  RenIsCategory .id      = Ren-id
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

-- ∈→≡ : x ∈ᵥ ` y → x ≡ y
-- ∈→≡  (here x=y) = x=y

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
  → (ρ : ∈Sub xs Θ) (σ : ∈Sub ys Θ)
  → Consistent ρ σ
  → ∈Sub (xs ++ ys) Θ
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

{-
∈sub-++-inv : {xs ys : Fins Ξ}
  → ∈Sub (xs ++ ys) Θ
  → Σ[ ρ ∈ ∈Sub xs Θ ] Σ[ σ ∈ ∈Sub ys Θ ] Consistent ρ σ
∈sub-++-inv γ@(f , r) = ⊆-∈Sub L.++⁺ˡ γ  , ⊆-∈Sub (L.++⁺ʳ _) γ ,
  λ x y → r (L.++⁺ˡ x) (L.++⁺ʳ _ y)
-}

⊑-refl : {xs : Fins Ξ}
  → (ρ : ∈Sub xs Θ) → ρ ⊑ ρ
⊑-refl ρ = (λ x → x) , ρ .proj₂

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
  {- begin
    lookup (tabulate (`_ ∘ ρ)) x
      ≡⟨ lookup∘tabulate (`_ ∘ ρ) x ⟩
    ` ρ x
      ≡⟨ cong `_ (sym $ lookup∘tabulate ρ x) ⟩
    ` lookup (tabulate ρ) x
      ∎
   -}
  rename-is-sub (op (i , ts)) = cong (op ∘ (i ,_)) (rename-is-subⁿ ts)

  rename-is-subⁿ
    : (ts : Tm Θ₁ ^ n)
    → ts ⟨ `_ ∘ ρ ⟩ ≡ ts ⟨ ρ ⟩
  rename-is-subⁿ []       = refl
  rename-is-subⁿ (t ∷ ts) = cong₂ _∷_ (rename-is-sub t) (rename-is-subⁿ ts)

{-
module _ {Θ : ℕ} where mutual
  linearlise : {t : Tm Θ}
    → Σ[ x ∈ Fin Θ ] (x ∈ᵥ t)
    → Fin (length (fv t))
  linearlise (_ , here _) = zero
  linearlise (_ , op x∈)  = linearliseⁿ (_ , x∈)

  linearliseⁿ : {ts : Tm Θ ^ n}
    → Σ[ x ∈ Fin Θ ] (x ∈ᵥₛ ts)
    → Fin (length (fvⁿ ts))
  linearliseⁿ {ts = t ∷ ts} (_ , head x∈) =
    subst Fin (sym $ L.length-++ (fv t))
    $ linearlise (_ , x∈) F.↑ˡ (length $ fvⁿ ts)
  linearliseⁿ {ts = t ∷ ts} (_ , tail x∈) =
    subst Fin (sym $ L.length-++ (fv t))
    $ (length $ fv t) F.↑ʳ linearliseⁿ (_ , x∈)

module _ {Θ : ℕ} where mutual
  reindex : {t : Tm Θ}
    → Fin (length (fv t))
    → Σ[ x ∈ Fin Θ ] (x ∈ᵥ t)
  reindex {t = ` x}         _ = x , here refl
  reindex {t = op (i , ts)} j = map₂ op (reindexⁿ j)

  reindexⁿ : {ts : Tm Θ ^ n}
    → Fin (length (fvⁿ ts))
    → Σ[ x ∈ Fin Θ ] (x ∈ᵥₛ ts)
  reindexⁿ {ts = t ∷ ts} i with F.splitAt (length (fv t)) (subst Fin (L.length-++ (fv t)) i)
  ... | inl i = map₂ head (reindex i)
  ... | inr j = map₂ tail (reindexⁿ j)
-}

-- ------------------------------------------------------------------------
-- -- Properties of Partial Substitution

-- psub-∷ : (g : PSub Ξ Θ) (t : Tm Ξ) (ts : Tm Ξ ^ n)
--   → psubⁿ g (t ∷ ts) ≡ just (u ∷ us) → psub g t ≡ just u × psubⁿ g ts ≡ just us
-- psub-∷ g t ts eq with psub g t 
-- ... | just u with psubⁿ g ts
-- psub-∷ g t ts refl | just u | just us = refl , refl

-- psubⁿ-op : (g : PSub Ξ Θ) {i : D .Op} (ts : Tm Ξ ^ D .rules i) (us : Tm Θ ^ D . rules i)
--   → psub g (op (i , ts)) ≡ just (op (i , us))
--   → psubⁿ g ts           ≡ just us
-- psubⁿ-op g ts us eq with psubⁿ g ts
-- psubⁿ-op g ts _ refl | just _ = refl

-- psubⁿ-op′ : (g : PSub Ξ Θ) {i j : D .Op} (ts : Tm Ξ ^ D .rules i) (us : Tm Θ ^ D . rules j)
--   → psub g (op (i , ts)) ≡ just (op (j , us))
--   → i ≡ j
-- psubⁿ-op′ g ts us eq with psubⁿ g ts
-- psubⁿ-op′ g ts _ refl | just _ = refl

-- module _ (g : PSub Ξ Θ) (σ : Sub Ξ Θ)  (g=σ : ∀ i → g i ≡ just (σ i)) where mutual
--   psub-sub : (t : Tm Ξ)
--     → psub g t ≡ just (t ⟨ σ ⟩)
--   psub-sub (` x)         = g=σ x
--   psub-sub (op (i , ts)) with psubⁿ g ts | psub-subⁿ ts
--   ... | just us | refl = refl

--   psub-subⁿ : (ts : Tm Ξ ^ n)
--     → psubⁿ g ts ≡ just (ts ⟨ σ ⟩)
--   psub-subⁿ []       = refl
--   psub-subⁿ (t ∷ ts) with psub g t | psub-sub t
--   ... | just u  | refl with psubⁿ g ts | psub-subⁿ ts
--   ... | just us | refl = refl
  
-- module _ (g : PSub Ξ Θ) (g↓ : ∀ i → ∃[ y ] g i ≡ just y) where mutual
--   totalise : Σ (Sub Ξ Θ) λ σ → (x : Fin Ξ) → g x ≡ just (σ x)
--   totalise = Partial→Total g g↓

--   totalise-soundness : Σ (Sub Ξ Θ) (λ σ → psub g t ≡ just (t ⟨ σ ⟩))
--   totalise-soundness {t = t} = map₂ (λ p → psub-sub g _ p t) totalise 

-- toPartial : (σ : Sub Ξ Θ)
--   → (t : Tm Ξ)
--   → Σ[ f ∈ PSub Ξ Θ ] psub f t ≡ just (t ⟨ σ ⟩)
-- toPartial σ t = just ∘ σ , psub-sub (just ∘ σ) σ (λ _ → refl) t 
-- ------------------------------------------------------------------------
-- -- Properties of Occurrence Substitution

-- module _ {Ξ Θ : ℕ} where mutual
--   eq? : (t : Tm Ξ) (u : Tm Θ)
--     → Dec (Σ[ f ∈ ∈-Sub t Θ ] ∈-sub t f ≡ u)
--   eq? (` x)         u             = yes ((λ { (here p) → u}) , refl)
--   eq? (op x)        (` y)         = no λ (f , P) → var≢op P
--   eq? (op (i , ts)) (op (j , us)) with i ≟ j
--   ... | no ¬p = no λ where
--     (_ , refl) → ¬p refl
--   ... | yes refl = map′
--     (λ (f , P) → (λ { (op x∈) → f x∈ }) , cong (op ∘ (i ,_)) P)
--     (λ (f , P) → (λ {i} x∈ → f (op x∈)) , op-inj₃ P) (eq?ⁿ ts us) 

--   eq?ⁿ : (ts : Tm Ξ ^ n) (us : Tm Θ ^ n)
--     → Dec (Σ[ f ∈ ∈-Subⁿ ts Θ ] ∈-subⁿ ts f ≡ us)
--   eq?ⁿ []       []       = yes ((λ ()) , refl)
--   eq?ⁿ (t ∷ ts) (u ∷ us) with eq? t u
--   ... | no ¬p = no λ where
--     (f , P) → ¬p (f ∘ head , V.∷-injectiveˡ P) 
--   ... | yes (f , P) with eq?ⁿ ts us
--   ... | no ¬q       = no λ where
--     (g , Q) → ¬q (g ∘ tail , V.∷-injectiveʳ Q)
--   ... | yes (g , Q) = yes ((λ { (head x∈) → f x∈ ; (tail x∈) → g x∈ }) , cong₂ _∷_ P Q)

-- ------------------------------------------------------------------------
-- -- Properties of Partial Substitution and Occurrence Substitution

-- postulate
--   dec-∈-irrelevance : (f : ∈-Sub t Θ) → Dec (∈-Irrelevant-Sub t f)

-- module _ (g : PSub Ξ Θ) where mutual
--   psub=∈-sub : (t : Tm Ξ) (f : ∈-Sub t Θ)
--     → (∀ {i} (x : i ∈ᵥ t) → g i ≡ just (f x))
--     → psub g t ≡ just (∈-sub t f)
--   psub=∈-sub (` x)         f P = P (here refl)
--   psub=∈-sub (op (i , ts)) f P
--     with psubⁿ g ts | psub=∈-subⁿ ts (f ∘ op) (P ∘ op)
--   ...  | just us    | refl = refl

--   psub=∈-subⁿ : (ts : Tm Ξ ^ n) (f : ∈-Subⁿ ts Θ)
--     → (∀ {i} (x : i ∈ᵥₛ ts) → g i ≡ just (f x))
--     → psubⁿ g ts ≡ just (∈-subⁿ ts f)
--   psub=∈-subⁿ []       _ _ = refl
--   psub=∈-subⁿ (t ∷ ts) f P
--     with psub g t | psub=∈-sub t (f ∘ head) (P ∘ head)
--   ...  | just u   | refl with psubⁿ g ts | psub=∈-subⁿ ts (f ∘ tail) (P ∘ tail)
--   ...                       | just us    | refl         = refl
  
-- module _ (g : PSub Ξ Θ) where mutual
--   psub→∈-sub : psub g t ≡ just u
--     → {i : Fin Ξ} (x : i ∈ᵥ t)
--     → Σ[ v ∈ Tm Θ ] (g i ≡ just v)
--   psub→∈-sub eq (here refl) = _ , eq
--   psub→∈-sub {op (i , ts)} {` _} eq (op x∈) with psubⁿ g ts
--   ... | just x  = ⊥-elim₀ (var≢op (just-injective eq))
--   ... | nothing = ⊥-elim₀ (nothing≢just eq)
--   psub→∈-sub {op (i , ts)} {op (j , us)} eq (op x∈) with psubⁿ-op′ g ts us eq
--   ... | refl = psub→∈-subⁿ (psubⁿ-op g ts us eq) x∈

--   psub→∈-subⁿ : psubⁿ g ts ≡ just us
--     → {i : Fin Ξ} (x : i ∈ᵥₛ ts) → Σ[ v ∈ Tm Θ ] (g i ≡ just v)
--   psub→∈-subⁿ {_} {t ∷ ts} {u ∷ us} eq (head x) = psub→∈-sub  (psub-∷ g t ts eq .proj₁) x
--   psub→∈-subⁿ {_} {t ∷ ts} {u ∷ us} eq (tail x) = psub→∈-subⁿ (psub-∷ g t ts eq .proj₂) x

-- module _ (g : PSub Ξ Θ) where
--   mutual
--     psub=∈-sub→pointwise : {t : Tm Ξ} (f : ∈-Sub t Θ)
--       → psub g t ≡ just (∈-sub t f)
--       → (∀ {i} (x : i ∈ᵥ t) → g i ≡ just (f x))
--     psub=∈-sub→pointwise               f eq (here refl) = eq
--     psub=∈-sub→pointwise {op (i , ts)} f eq (op x∈)     =
--       psub=∈-sub→pointwiseⁿ (f ∘ op) (psubⁿ-op g ts _ eq) x∈

--     psub=∈-sub→pointwiseⁿ  : {ts : Tm Ξ ^ n} (f : ∈-Subⁿ ts Θ)
--       → psubⁿ g ts ≡ just (∈-subⁿ ts f)
--       → (∀ {i} (x : i ∈ᵥₛ ts) → g i ≡ just (f x))
--     psub=∈-sub→pointwiseⁿ {_} {t ∷ ts} f eq (head x∈) =
--       psub=∈-sub→pointwise  (f ∘ head) (psub-∷ g t ts eq .proj₁) x∈
--     psub=∈-sub→pointwiseⁿ {_} {t ∷ ts} f eq (tail x∈) =
--       psub=∈-sub→pointwiseⁿ (f ∘ tail) (psub-∷ g t ts eq .proj₂) x∈

--   PSub→∈-Irrelevant-Sub : (f : ∈-Sub t Θ)
--     → psub g t ≡ just (∈-sub t f)
--     → ∈-Irrelevant-Sub t f
--   PSub→∈-Irrelevant-Sub f eq {i} x y = just-injective $ begin
--     just (f x)
--       ≡⟨ (sym $ psub=∈-sub→pointwise f eq x) ⟩
--     g i 
--       ≡⟨ psub=∈-sub→pointwise f eq y ⟩
--     just (f y)
--       ∎

-- module _ {t : Tm Ξ} (f : ∈-Sub t Θ ) where
--   ∀tᵢ=fₓ : ∈-Irrelevant-Sub t f
--     → (i : Fin Ξ) → Σ[ tᵢ ∈ Maybe (Tm Θ) ] ((x : i ∈ᵥ t) → tᵢ ≡ just (f x))
--   ∀tᵢ=fₓ P i with i ∈ᵥ? t
--   ... | no x∉  = nothing     , λ x∈ → ⊥-elim₀ (x∉ x∈)
--   ... | yes x∈ = just (f x∈) , λ x∈′ → cong just (P x∈ x∈′)
  
--   ∃σᵢ=fₓ : ∈-Irrelevant-Sub t f
--     → Σ[ g ∈ PSub Ξ Θ ] (∀ {i} (x : i ∈ᵥ t) → g i ≡ just (f x))
--   ∃σᵢ=fₓ P = (λ i → ∀tᵢ=fₓ P i .proj₁) , ∀tᵢ=fₓ P _ .proj₂

--   ∈-Irrelevant-Sub→PSub
--     : Dec (∈-Irrelevant-Sub t f)
--     → Dec (Σ[ g ∈ PSub Ξ Θ ] (∀ {i} (x : i ∈ᵥ t) → g i ≡ just (f x)))
--   ∈-Irrelevant-Sub→PSub = map′ ∃σᵢ=fₓ
--     (λ (σ , P) x y → M.just-injective $ begin
--       just (f x)
--         ≡⟨ sym (P x) ⟩
--       _
--         ≡⟨ P y ⟩
--       just (f y)
--         ∎)
  
-- module _ {Ξ Θ : ℕ} where mutual
--   PSub→∈-Sub : (t : Tm Ξ) (u : Tm Θ) (g : PSub Ξ Θ) → psub g t ≡ just u
--     → Σ[ f ∈ ∈-Sub t Θ ] (∈-sub t f ≡ u)
--   PSub→∈-Sub t u g eq =
--     let f = λ {i : Fin _} (x : i ∈ᵥ t) → psub→∈-sub g eq x .proj₁
--         P = λ {i : Fin _} (x : i ∈ᵥ t) → psub→∈-sub g eq x .proj₂ in
--     f , just-injective (begin
--       just (∈-sub t _)
--         ≡⟨ sym (psub=∈-sub g t f P) ⟩ 
--       psub g t
--         ≡⟨ eq ⟩
--       just u
--         ∎)

-- module _ (t : Tm Ξ) (u : Tm Θ) where
--   peq? : Dec (Σ[ g ∈ PSub Ξ Θ ] psub g t ≡ just u)
--   peq? with eq? t u
--   ... | no ¬p = no (¬p ∘ uncurry (PSub→∈-Sub t u))
--   ... | yes (f , p) with dec-∈-irrelevance f
--   ... | no ¬q = no (¬q ∘ λ (g , eq) → PSub→∈-Irrelevant-Sub g f (begin
--     psub g t
--       ≡⟨ eq ⟩
--     just u
--       ≡⟨ sym (cong just p) ⟩
--     just (∈-sub t f)
--       ∎))
--   ... | yes q = let g  = ∃σᵢ=fₓ f q .proj₁
--                     gq = ∃σᵢ=fₓ f q .proj₂ in
--                 yes (g , (begin
--     psub g t
--       ≡⟨ psub=∈-sub _ t f gq ⟩
--     just (∈-sub t f)
--       ≡⟨ cong just p ⟩
--     just u
--       ∎))

-- {-
-- module _ (f g : PSub Ξ Θ) (p : ∀ i → f i ≡ g i) where mutual
--   psub-cong : (t : Tm Ξ) 
--     → psub f t ≡ psub g t
--   psub-cong (`  x)        = p x
--   psub-cong (op (i , ts)) with psubⁿ f ts | psubⁿ g ts | psub-congⁿ ts
--   ... | nothing | nothing | _ = refl
--   ... | just ts | just ts′ | refl = refl

--   psub-congⁿ : (ts : Tm Ξ ^ n)
--     → psubⁿ f ts ≡ psubⁿ g ts
--   psub-congⁿ []       = refl
--   psub-congⁿ (t ∷ ts) with psub f t | psub g t | psub-cong t 
--   ... | nothing  | nothing  | _ = refl
--   ... | just u₁  | just u₂  | refl with psubⁿ f ts | psubⁿ g ts | psub-congⁿ ts
--   ...                                 | nothing    | nothing    | refl = refl
--   ...                                 | just us₁   | just us₂   | refl = refl

-- module _{Ξ : ℕ} where mutual
--   ∈-sub-cong : (t : Tm Ξ) (f g : ∈-Sub t Θ)
--     → (∀ {i} (x : i ∈ᵥ t) → f x ≡ g x)
--     → ∈-sub t f ≡ ∈-sub t g
--   ∈-sub-cong (` x)         f g p = p (here refl)
--   ∈-sub-cong (op (i , ts)) f g p = cong (op ∘ (i ,_))
--     (∈-sub-congⁿ ts (f ∘ op) (g ∘ op) (p ∘ op))

--   ∈-sub-congⁿ : (ts : Tm Ξ ^ n) (f g : ∈-Subⁿ ts Θ)
--     → (∀ {i} (x : i ∈ᵥₛ ts) → f x ≡ g x)
--     → ∈-subⁿ ts f ≡ ∈-subⁿ ts g
--   ∈-sub-congⁿ []       f g p = refl
--   ∈-sub-congⁿ (t ∷ ts) f g p = cong₂ _∷_
--     (∈-sub-cong t (f ∘ head) (g ∘ head) (p ∘ head))
--     (∈-sub-congⁿ ts (f ∘ tail) (g ∘ tail) (p ∘ tail))
-- -}
