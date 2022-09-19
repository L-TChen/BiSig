open import Prelude

import Syntax.Simple.Description as S
open import Syntax.BiTyped.Description

import Theory.ModeCorrectness.Description as B

module Theory.ModeCorrectness.Term {SD : S.Desc}
  (Id : Set) (_≟Id_ : (x y : Id) → Dec (x ≡ y))
  (D : Desc {SD}) (mc : B.ModeCorrect Id D) where

open B {SD} Id

import      Data.Vec                     as V
import      Data.List.Relation.Unary.All as A
open import Data.List.Relation.Unary.Any.Properties

open import Syntax.NamedContext Id
open import Syntax.NamedContext.Decidable _≟Id_

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tms to TExps; Tm₀ to T; _≟_ to _≟T_)
open import Syntax.Simple.Properties         {SD}

import      Syntax.BiTyped.Raw.Functor       {SD} Id as R
open import Syntax.BiTyped.Raw.Term          {SD} Id D
open import Syntax.BiTyped.Extrinsic.Functor {SD} Id D
open import Syntax.BiTyped.Extrinsic.Term    {SD} Id D

private variable
  Ξ     : ℕ
  A B   : T
  xs    : List (Fin Ξ)
  Γ     : Context T
  Ds    : ArgsD Ξ
  AD    : ArgD Ξ
  σ σ₁ σ₂ : Sub₀ Ξ
  m     : Mode

MC : {CD : ConD} → (CD ∈ D) → _
MC i = A.lookup mc i

mutual
  -- a result of syntax directedness
  uniq-⊢
    : {t : Raw m}
    → (⊢t : ⊢⇄ m A Γ t) (⊢u : ⊢⇄ m B Γ t)
    → A ≡ B
  uniq-⊢ (⊢` x)       (⊢` y)       = uniq-∈ x y
  uniq-⊢ (⊢⦂ ⊢t)      (⊢⦂ ⊢u)      = refl
  uniq-⊢ (⊢⇉ ⊢t refl) (⊢⇉ ⊢u refl) = uniq-⊢ ⊢t ⊢u
  uniq-⊢ {Check} (⊢op (ι Check C Ds , i , _) (_ , refl , ⊢ts)) (⊢op _ (_ , refl , ⊢us)) = {!   !}
  uniq-⊢ {Infer} (⊢op (ι Infer C Ds , i , _) (_ , refl , ⊢ts)) (⊢op _ (_ , refl , ⊢us)) = {!   !}

  uniq-⊢ⁿ
    : (Ds : ArgsD Ξ) (xs₀ : List {!   !})
    → ModeCorrectᵃˢ xs₀ Ds
    → {ts : R.⟦ Ds ⟧ᵃˢ Raw}
    → (⊢ts : (⟦ Ds ⟧ᵃˢ Raw , ⊢⇄) σ₁ Γ ts)
    → (⊢us : (⟦ Ds ⟧ᵃˢ Raw , ⊢⇄) σ₁ Γ ts) 
    → ∀ {x} → x ∈ Known xs₀ Ds
    → V.lookup σ₁ x ≡ V.lookup σ₂ x
  uniq-⊢ⁿ ∅ xs₀ SDs ⊢ts ⊢us i = {!   !}
  uniq-⊢ⁿ (Θ ⊢[ m ] _  ∙ Ds) xs₀ SDs ⊢ts ⊢us i = {!   !}
  -- decompose this lemma into some more conceptual results
  uniq-⇉
    : {t : Raw⇉}
    → (⊢t : Γ ⊢ t ⇉ A) (⊢u : Γ ⊢ t ⇉ B)
    → A ≡ B
  uniq-⇉ (⊢` x)   (⊢` y)  = uniq-∈ x y
  uniq-⇉ (⊢⦂ ⊢t)  (⊢⦂ ⊢u) = refl
  uniq-⇉ (⊢op (ι Infer C Ds , i , _) (_ , refl , ⊢ts)) (⊢op _ (_ , refl , ⊢us)) =
    let (C⊆xs , _ , SDs) = MC i in
    ≡-fv C λ x → uniq-⇉Map Ds SDs ⊢ts ⊢us (C⊆xs x)

  uniq-⇉Map
    : (Ds : ArgsD Ξ)
    → ModeCorrectᵃˢ ∅ Ds
    → {ts : R.⟦ Ds ⟧ᵃˢ Raw}
    → (⊢ts : (⟦ Ds ⟧ᵃˢ Raw , ⊢⇄) σ₁ Γ ts)
    → (⊢us : (⟦ Ds ⟧ᵃˢ Raw , ⊢⇄) σ₂ Γ ts)
    → ∀ {x} → x ∈ Known ∅ Ds
    → V.lookup σ₁ x ≡ V.lookup σ₂ x
  uniq-⇉Map ∅                     _             _          _          ()
  uniq-⇉Map (_ ⊢[ Check ] _ ∙ Ds) (_ , _ , SDs) (_ , ⊢ts)  (_ , ⊢us) =
    uniq-⇉Map Ds SDs ⊢ts ⊢us
  uniq-⇉Map (Θ ⊢[ Infer ] C ∙ Ds) (SD , SDs)    (⊢t , ⊢ts) (⊢u , ⊢us) i with ++⁻ (fv C) i
  ... | inl j = uniq-⇉Mapᵃ C Θ SD ⊢t ⊢u (uniq-⇉Map Ds SDs ⊢ts ⊢us) j
  ... | inr j = uniq-⇉Map Ds SDs ⊢ts ⊢us j

  uniq-⇉Mapᵃ
    : (C : TExp Ξ) (Θ : TExps Ξ)
    → ModeCorrectᵃ xs Θ
    → {t : R.⟦ Θ ⟧ᵃ Raw Infer}
    → (⊢t : (⟦ Θ ⟧ᵃ Raw , ⊢⇄ Infer (⟪ σ₁ ⟫ C)) σ₁ Γ t)
    → (⊢u : (⟦ Θ ⟧ᵃ Raw , ⊢⇄ Infer (⟪ σ₂ ⟫ C)) σ₂ Γ t)
    → (∀ {x} → x ∈ xs → V.lookup σ₁ x ≡ V.lookup σ₂ x)
    → ∀ {x} → x ∈ fv C
    → V.lookup σ₁ x ≡ V.lookup σ₂ x
  uniq-⇉Mapᵃ C ∅       _           ⊢t ⊢u f = ≡-fv-inv C (uniq-⇉ ⊢t ⊢u)
  uniq-⇉Mapᵃ C (A ∙ Θ) (A⊆xs , SD) ⊢t ⊢u f = let A₁=A₂ = ≡-fv A λ x∈fvA → f (A⊆xs x∈fvA) in 
    uniq-⇉Mapᵃ C Θ SD (subst (λ A → (⟦ Θ ⟧ᵃ _ , _) _ (_ ⦂ A , _) _) A₁=A₂ ⊢t) ⊢u f

-- ¬switch
--   : {t : Raw⇉}
--   → Γ ⊢ t ⇉ A
--   → A ≢ B
--   → ¬ (Γ ⊢ (t ↑) ⇇ B)
-- ¬switch ⊢t A≠B (⊢⇉ ⊢t′ A=B) rewrite uniq-⇉ ⊢t ⊢t′ = A≠B A=B

-- mutual
--   synthesise
--     : (Γ : Context T) (t : Raw⇉)
--     → Dec (∃[ A ] Γ ⊢ t ⇉ A)
--   synthesise Γ (` x)   with lookup Γ x
--   ... | no ¬p       = no λ where (A , ⊢` x∈) → ¬p (A , x∈)
--   ... | yes (A , x) = yes (A , ⊢` x)
--   synthesise Γ (t ⦂ A) with check Γ t A
--   ... | no ¬p = no λ where (B , ⊢⦂ ⊢t) → ¬p ⊢t
--   ... | yes p = yes (A , ⊢⦂ p)
--   synthesise Γ (op (ι Infer C Ds , i , ts)) with MC i
--   ... | (C⊆xs , _ , SDs) with synthesiseᵃˢ Ds SDs Γ ts
--   ... | no ¬p = no λ where (A , ⊢op _ (σ , refl , ⊢ts)) → ¬p (σ , ⊢ts)
--   ... | yes (σ , ⊢ts) = yes (⟪ σ ⟫ C , ⊢op (_ , i , ts) (σ , refl , ⊢ts))

--   check
--     : (Γ : Context T) (t : Raw⇇) (A : T)
--     → Dec (Γ ⊢ t ⇇ A)
--   check Γ (t ↑)  A with synthesise  Γ t
--   ... | no ¬p = no λ where (⊢⇉ ⊢t refl) → ¬p (A , ⊢t)
--   ... | yes (B , ⊢t) with B ≟T A
--   ... | no ¬q   = no (¬switch ⊢t ¬q)
--   ... | yes A=B = yes (⊢⇉ ⊢t A=B)
--   check Γ (op (ι Check C Ds , i , ts)) A with checkᵃˢ C A Ds (MC i) Γ ts
--   ... | no ¬p = no λ where (⊢op _ p) → ¬p p
--   ... | yes (σ , eq , ⊢ts) = yes (⊢op (_ , i , ts) (σ , eq , ⊢ts))

--   synthesiseᵃˢ
--     : (Ds : ArgsD Ξ)
--     → ModeCorrectᵃˢ ∅ Ds
--     → (Γ : Context T) (ts : R.⟦ Ds ⟧ᵃˢ Raw)
--     → Dec (∃[ σ ] (⟦ Ds ⟧ᵃˢ Raw , ⊢⇄) σ Γ ts)
--   synthesiseᵃˢ DS SDs Γ ts = {!   !}

--   synthesiseSubᵃˢ
--     : (Ds : ArgsD Ξ)
--     → ModeCorrectᵃˢ ∅ Ds
--     → (Γ : Context T) (ts : R.⟦ Ds ⟧ᵃˢ Raw)
--     → ∀ {x} → (i : x ∈ Known ∅ Ds) → {!   !}
--   synthesiseSubᵃˢ ∅ _ _ _ ()
--   synthesiseSubᵃˢ (Θ ⊢[ Infer ] C ∙ Ds) Mc Γ ts i = {!   !}
--   synthesiseSubᵃˢ (Θ ⊢[ Check ] C ∙ Ds) Mc Γ ts i = {!   !}

--   checkᵃˢ
--     : (C : TExp Ξ)
--     → (A : T)
--     → (Ds : ArgsD Ξ)
--     → ModeCorrectᵃˢ (fv C) Ds
--     → (Γ : Context T) (ts : R.⟦ Ds ⟧ᵃˢ Raw)
--     → Dec (∃[ σ ] (⟪ σ ⟫ C ≡ A × (⟦ Ds ⟧ᵃˢ Raw , ⊢⇄) σ Γ ts))
--   checkᵃˢ C A DS SDs Γ ts = {!   !}