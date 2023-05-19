{-# OPTIONS --with-K --rewriting #-}
open import Prelude
  hiding (lookup)

import Syntax.Simple.Description as S
import Syntax.BiTyped.Description as B

import Theory.ModeCorrectness.Description as M

module Theory.ModeCorrectness.Term {SD : S.Desc}
  (Id : Set) (_≟Id_ : (x y : Id) → Dec (x ≡ y))
  (D : B.Desc SD) (mc : M.ModeCorrect SD Id D) where

open M SD Id
open B SD

import      Data.List.Relation.Unary.All as A

open import Syntax.NamedContext           SD Id
open import Syntax.NamedContext.Decidable _≟Id_

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tms to TExps; Sub to TSub)
open import Syntax.Simple.Association            SD
open import Syntax.Simple.Properties             SD
open import Syntax.Simple.Unification            SD
open import Syntax.Simple.Unification.Properties SD

import      Syntax.BiTyped.Raw.Functor           SD Id as R
open import Syntax.BiTyped.Raw.Term                 Id D
open import Syntax.BiTyped.Extrinsic.Functor     SD Id
open import Syntax.BiTyped.Extrinsic.Term           Id D
open import Syntax.BiTyped.Extrinsic.Properties     Id D

import Syntax.BiTyped.Intrinsic.Functor  {SD}       as I
open import Syntax.BiTyped.Intrinsic.Term            D

open import Theory.Ontologisation.Context         Id

private variable
  n m l : ℕ
  A B   : TExp n
  xs    : List (Fin n)
  Γ     : Cxt   n
  Ds    : ArgsD n
  AD    : ArgD  n
  σ σ₁ σ₂ ρ γ : TSub n m
  mod     : Mode
  t u     : Raw m mod

-- MC : {CD : ConD} → (CD ∈ D) → _
-- MC i = A.lookup mc i

mutual
  -- It should follow from syntax directedness:
  -- decompose this lemma into some more conceptual results
  uniq-⇉
    : {t : Raw⇉ m}
    → (⊢t : Γ ⊢ t ⇉ A) (⊢u : Γ ⊢ t ⇉ B)
    → A ≡ B
  uniq-⇉ (⊢` x)   (⊢` y)  = uniq-∈ x y
  uniq-⇉ (⊢⦂ ⊢t refl)  (⊢⦂ ⊢u refl) = refl
  uniq-⇉ (⊢op (i , meq , rs) (ts , refl , ⊢ts)) (⊢op _ (us , refl , ⊢us)) =
    uniq-⇉ᶜ (mc i) meq ⊢ts ⊢us

  uniq-⇉ᶜ : ∀ {D} → ModeCorrectᶜ D → ConD.mode D ≡ Infer
          → ∀ {rs ts us}
          → ⟦ ConD.args D ⟧ᵃˢ (Raw m) ⊢⇄ ts Γ rs
          → ⟦ ConD.args D ⟧ᵃˢ (Raw m) ⊢⇄ us Γ rs
          → ConD.type D ⟨ ts ⟩ ≡ ConD.type D ⟨ us ⟩
  uniq-⇉ᶜ {D = D} (C⊆xs , _ , SDs) refl ⊢ts ⊢us =
    ≡-fv _ _ (ConD.type D) λ x → uniq-⇉Map _ SDs ⊢ts ⊢us (C⊆xs x)

  uniq-⇉Map
    : (Ds : ArgsD n)
    → ModeCorrectᵃˢ [] Ds
    → {ts : R.⟦ Ds ⟧ᵃˢ (Raw m)}
    → (⊢ts : ⟦ Ds ⟧ᵃˢ (Raw m) ⊢⇄ σ₁ Γ ts)
    → (⊢us : ⟦ Ds ⟧ᵃˢ (Raw m) ⊢⇄ σ₂ Γ ts)
    → ∀ {x} → x ∈ Known [] Ds
    → V.lookup σ₁ x ≡ V.lookup σ₂ x -- σ₁ x ≡ σ₂ x
  uniq-⇉Map []                    _             _          _          ()
  uniq-⇉Map (_ ⊢[ Check ] _ ∷ Ds) (_ , _ , SDs) (_ , ⊢ts)  (_ , ⊢us) =
    uniq-⇉Map Ds SDs ⊢ts ⊢us
  uniq-⇉Map (Θ ⊢[ Infer ] C ∷ Ds) (SD , SDs)    (⊢t , ⊢ts) (⊢u , ⊢us) i with ∈-++⁻ (fv C) i
  ... | inl j = uniq-⇉Mapᵃ C Θ SD ⊢t ⊢u (uniq-⇉Map Ds SDs ⊢ts ⊢us) j
  ... | inr j = uniq-⇉Map Ds SDs ⊢ts ⊢us j

  uniq-⇉Mapᵃ
    : (C : TExp n) (Θ : TExps n)
    → ModeCorrectᵃ xs Θ
    → {t : R.⟦ Θ ⟧ᵃ (Raw m Infer)}
    → (⊢t : ⟦ Θ ⟧ᵃ (Raw m) (⊢⇄ Infer (C ⟨ σ₁ ⟩)) σ₁ Γ t)
    -- (⟦ Θ ⟧ᵃ (Raw m) ⊢⇄ Infer (⟪ σ₁ ⟫ C)) σ₁ Γ t)
    → (⊢u : ⟦ Θ ⟧ᵃ (Raw m) (⊢⇄ Infer (C ⟨ σ₂ ⟩)) σ₂ Γ t)
    -- (⟦ Θ ⟧ᵃ (Raw m) ⊢⇄ Infer (⟪ σ₂ ⟫ C)) σ₂ Γ t)
    → (∀ {x} → x ∈ xs → V.lookup σ₁ x ≡ V.lookup σ₂ x)
    → ∀ {x} → x ∈ fv C
    → V.lookup σ₁ x ≡ V.lookup σ₂ x
  uniq-⇉Mapᵃ C []       _           ⊢t ⊢u f = ≡-fv-inv C (uniq-⇉ ⊢t ⊢u)
  uniq-⇉Mapᵃ {σ₁ = σ₁} {σ₂ = σ₂} C (A ∷ Θ) (A⊆xs , SD) ⊢t ⊢u f =
    let A₁=A₂ = ≡-fv σ₁ σ₂ A λ x∈fvA → f (A⊆xs x∈fvA) in
    uniq-⇉Mapᵃ C Θ SD (subst (λ A → (⟦ Θ ⟧ᵃ _ _) _ (_ ⦂ A , _) _) A₁=A₂ ⊢t) ⊢u f

¬switch
  : {t : Raw⇉ m}
  → Γ ⊢ t ⇉ A
  → A ≢ B
  → ¬ (Γ ⊢ (t ↑) ⇇ B)
¬switch ⊢t A≠B (⊢⇉ ⊢t′ A=B) rewrite uniq-⇉ ⊢t ⊢t′ = A≠B A=B

------------------------------------------------------------------------------
-- A type checker

module _ {m : ℕ} where mutual
  synthesise
    : (Γ : Cxt m) (t : Raw⇉ m) (σ : AList m n)
    → Maybe (∃₂ λ k (σ : AList m k) → Σ[ A ∈ TExp m ] {!? ⊢ ?!}) -- Γ ⟨ σ ⟩ ⊢ t ⟨ σ ⟩ ⇉ A ⟨ σ ⟩)

  inherit
    : (Γ : Cxt m) (t : Raw⇇ m) (σ : AList m n) (A : TExp m)
    → Maybe (∃₂ λ k (σ : AList m k) → {!!} ) -- Γ ⟨ σ ⟩ ⊢ t ⟨ σ ⟩ ⇇ A ⟨ σ ⟩)

  synthesise = {!!}
  inherit    = {!!}
--   synthetise Γ (` x)   σ with lookup Γ x
--   ... | no _         = nothing
--   ... | yes (A , x∈) = just ((_ , σ , A , ⊢` (sub-∈ (toSub σ) x∈)))

--   synthetise Γ (t ⦂ A) σ with inherit Γ t σ A
--   ... | nothing = nothing
--   ... | just (n , σ , ⊢t) = just (_ , σ , A , ⊢⦂ ⊢t refl)

--   synthetise Γ (op (i , eq , ts)) σ = {!!}

--   inherit Γ (t ↑) σ A  with synthetise Γ t σ
--   ... | nothing = nothing
--   ... | just (_ , ρ , B , ⊢t) with amgu⁺ A B ρ
--   ... | inr _ = nothing
--   ... | inl (_ , γ , A≈B , min) = just (_ , ρ ⨟ γ , ⊢⇉ {!!} (sym A≈B))

--   inherit Γ (op (i , eq , ts)) σ A = {!!}

-- ------------------------------------------------------------------------------
-- -- A proof-relevant type checker

-- module _ {m : ℕ} where mutual
--   synthetise⁺
--     : (Γ : Cxt m) (t : Raw⇉ m) (σ : AList m n)
--     → Dec (∃[ k ] Σ[ σ ∈ AList m k ] Σ[ A ∈ TExp m ]
--         Γ ⟨ σ ⟩ ⊢ t ⟨ σ ⟩ ⇉ A ⟨ σ ⟩)
--   inherit⁺
--     : (Γ : Cxt m) (t : Raw⇇ m) (σ : AList m n) (A : TExp m)
--     → Dec (∃[ k ] Σ[ σ ∈ AList m k ]
--         Γ ⟨ σ ⟩ ⊢ t ⟨ σ ⟩ ⇇ A ⟨ σ ⟩)

--   synthetise⁺ Γ (` x)   σ with lookup Γ x
--   ... | no ¬p = no λ where (l , σ′ , A , ⊢` y) → subst-∈→∈ Γ x ¬p (toSub σ′) (_ , y)
--   ... | yes (A , x) = yes (_ , σ , A , ⊢` (sub-∈ (toSub σ) x))
--   synthetise⁺ Γ (t ⦂ A) σ with inherit⁺ Γ t σ A
--   ... | no ¬p = no λ where (n , σ , B , ⊢⦂ ⊢t _) → ¬p (_ , σ , ⊢t)
--   ... | yes (n , σ , ⊢t) = yes (_ , σ , A , ⊢⦂ ⊢t refl)
--   synthetise⁺ Γ (op x)  σ = {!!}

--   inherit⁺ Γ (t ↑)  σ A with synthetise⁺ Γ t σ
--   ... | no ¬p = no λ where (n , σ′ , ⊢⇉ ⊢t refl) → ¬p (n , σ′ , A , ⊢t)
--   ... | yes (l , σ , B , ⊢t)  = {!!} -- we need to compare A and B, if A and B are not unifiable, then amgu needs to provide a proof of A ≢ B
-- --  ... | yes (l , σ , B , ⊢t)  with amgu A B (_ , σ)
-- --  ... | nothing       = no  λ where (_ , σ′ , ⊢t′) → ¬switch ⊢t {!!} {!⊢t′!}
-- --  ... | just (l , σ′) = yes (l , σ′ , ⊢⇉ {!!} {!!})
--   inherit⁺ Γ (op x) σ A = {!!}
