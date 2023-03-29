{-# OPTIONS --with-K #-} 
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

open import Syntax.NamedContext           SD Id
open import Syntax.NamedContext.Decidable _≟Id_

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tms to TExps; Sub to TSub; _≟_ to _≟T_)
open import Syntax.Simple.Association        SD
open import Syntax.Simple.Properties         {SD}
open import Syntax.Simple.Unification        {SD}

import      Syntax.BiTyped.Raw.Functor       {SD} Id as R
open import Syntax.BiTyped.Raw.Term               Id D
open import Syntax.BiTyped.Extrinsic.Functor      Id D
open import Syntax.BiTyped.Extrinsic.Term         Id D

private variable
  n m l : ℕ
  A B   : TExp n
  xs    : List (Fin n)
  Γ     : Cxt n
  Ds    : ArgsD n
  AD    : ArgD n
  σ σ₁ σ₂ : TSub n m
  mod     : Mode

MC : {CD : ConD} → (CD ∈ D) → _
MC i = A.lookup mc i

mutual
  -- It should follow from syntax directedness:
  -- decompose this lemma into some more conceptual results
  uniq-⇉
    : {t : Raw⇉ m}
    → (⊢t : Γ ⊢ t ⇉ A) (⊢u : Γ ⊢ t ⇉ B)
    → A ≡ B
  uniq-⇉ (⊢` x)   (⊢` y)  = uniq-∈ x y
  uniq-⇉ (⊢⦂ ⊢t refl)  (⊢⦂ ⊢u refl) = refl
  uniq-⇉ {t = op (ι Infer C Ds , i , refl , _)} (⊢op _ (_ , refl , ⊢ts)) (⊢op _ (_ , refl , ⊢us)) =
    let (C⊆xs , _ , SDs) = MC i in
    ≡-fv _ _ C λ x → uniq-⇉Map Ds SDs ⊢ts ⊢us (C⊆xs x)

  uniq-⇉Map
    : (Ds : ArgsD n)
    → ModeCorrectᵃˢ ∅ Ds
    → {ts : R.⟦ Ds ⟧ᵃˢ (Raw m)}
    → (⊢ts : ⟦ Ds ⟧ᵃˢ (Raw m) ⊢⇄ σ₁ Γ ts)
    → (⊢us : ⟦ Ds ⟧ᵃˢ (Raw m) ⊢⇄ σ₂ Γ ts)
    → ∀ {x} → x ∈ Known ∅ Ds
    → V.lookup σ₁ x ≡ V.lookup σ₂ x -- σ₁ x ≡ σ₂ x
  uniq-⇉Map ∅                     _             _          _          ()
  uniq-⇉Map (_ ⊢[ Check ] _ ∙ Ds) (_ , _ , SDs) (_ , ⊢ts)  (_ , ⊢us) =
    uniq-⇉Map Ds SDs ⊢ts ⊢us
  uniq-⇉Map (Θ ⊢[ Infer ] C ∙ Ds) (SD , SDs)    (⊢t , ⊢ts) (⊢u , ⊢us) i with ++⁻ (fv C) i
  ... | inl j = uniq-⇉Mapᵃ C Θ SD ⊢t ⊢u (uniq-⇉Map Ds SDs ⊢ts ⊢us) j
  ... | inr j = uniq-⇉Map Ds SDs ⊢ts ⊢us j

  uniq-⇉Mapᵃ
    : (C : TExp n) (Θ : TExps n)
    → ModeCorrectᵃ xs Θ
    → {t : R.⟦ Θ ⟧ᵃ (Raw m Infer)}
    → (⊢t : ⟦ Θ ⟧ᵃ (Raw m) (⊢⇄ Infer (⟪ σ₁ ⟫ C)) σ₁ Γ t)
    -- (⟦ Θ ⟧ᵃ (Raw m) ⊢⇄ Infer (⟪ σ₁ ⟫ C)) σ₁ Γ t)
    → (⊢u : ⟦ Θ ⟧ᵃ (Raw m) (⊢⇄ Infer (⟪ σ₂ ⟫ C)) σ₂ Γ t)
    -- (⟦ Θ ⟧ᵃ (Raw m) ⊢⇄ Infer (⟪ σ₂ ⟫ C)) σ₂ Γ t)
    → (∀ {x} → x ∈ xs → V.lookup σ₁ x ≡ V.lookup σ₂ x)
    → ∀ {x} → x ∈ fv C
    → V.lookup σ₁ x ≡ V.lookup σ₂ x
  uniq-⇉Mapᵃ C ∅       _           ⊢t ⊢u f = ≡-fv-inv C (uniq-⇉ ⊢t ⊢u)
  uniq-⇉Mapᵃ {σ₁ = σ₁} {σ₂ = σ₂} C (A ∙ Θ) (A⊆xs , SD) ⊢t ⊢u f =
    let A₁=A₂ = ≡-fv σ₁ σ₂ A λ x∈fvA → f (A⊆xs x∈fvA) in
    uniq-⇉Mapᵃ C Θ SD (subst (λ A → (⟦ Θ ⟧ᵃ _ _) _ (_ ⦂ A , _) _) A₁=A₂ ⊢t) ⊢u f

¬switch
  : {t : Raw⇉ m}
  → Γ ⊢ t ⇉ A
  → A ≢ B
  → ¬ (Γ ⊢ (t ↑) ⇇ B)
¬switch ⊢t A≠B (⊢⇉ ⊢t′ A=B) rewrite uniq-⇉ ⊢t ⊢t′ = A≠B A=B

sub-∈ : ∀ {x} (σ : TSub m n)
  → x ⦂ A         ∈ Γ
  → x ⦂ ⟪ σ ⟫ A ∈ ⟪ σ ⟫cxt Γ
sub-∈ σ zero        = zero 
sub-∈ σ (suc ¬p x∈) = suc ¬p (sub-∈ σ x∈)

subst-∈→∈
  : ∀ (Γ : Cxt m) x
  → ¬ (∃[ A ] (x ⦂ A ∈ Γ))
  → (σ : TSub m n)
  → ¬ (∃[ B ] (x ⦂ B ∈ ⟪ σ ⟫cxt Γ))
subst-∈→∈ (_ ∙ _)       _ ¬∃ σ (D , zero)      = ¬∃ (_ , zero)
subst-∈→∈ ((y , C) ∙ Γ) x ¬∃ σ (D , suc ¬p x∈) =
  subst-∈→∈ Γ x (λ where (_ , x∈) → ¬∃ (_ , suc ¬p x∈)) σ (_ , x∈)

mutual
  synthetise
    : (Γ : Cxt m)              (t : Raw⇉ m) (σ : AList m n)
    → Dec (∃[ k ] Σ[ σ ∈ AList m k ] Σ[ A ∈ TExp m ] (⟪ toSub σ ⟫cxt Γ ⊢ ⟪ toSub σ ⟫ₜ t ⇉ ⟪ toSub σ ⟫ A))
  inherit
    : (Γ : Cxt m) (A : TExp m) (t : Raw⇇ m) (σ : AList m n)
    → Dec (∃[ k ] (Σ[ σ ∈ AList m k ] (⟪ toSub σ ⟫cxt Γ ⊢ ⟪ toSub σ ⟫ₜ t ⇇ ⟪ toSub σ ⟫ A)))

  synthetise Γ (` x)   σ with lookup Γ x
  ... | no ¬p = no λ where (l , σ′ , A , ⊢` y) → subst-∈→∈ Γ x ¬p (toSub σ′) (_ , y)
  ... | yes (A , x) = yes (_ , σ , A , ⊢` (sub-∈ (toSub σ) x))
  synthetise Γ (t ⦂ A) σ with inherit Γ A t σ
  ... | no ¬p = no λ where (n , σ , B , ⊢⦂ ⊢t _) → ¬p (_ , σ , ⊢t)
  ... | yes (n , σ , ⊢t) = yes (_ , σ , A , ⊢⦂ ⊢t refl)
  synthetise Γ (op x)  σ = {!!}

  inherit Γ A (t ↑)  σ with synthetise Γ t σ
  ... | no ¬p = no λ where (n , σ′ , ⊢⇉ ⊢t refl) → ¬p (n , σ′ , A , ⊢t)
  ... | yes (l , σ , B , ⊢t)  = {!!} -- we need to compare A and B, if A and B are not unifiable, then amgu needs to provide a proof of A ≢ B
--  ... | yes (l , σ , B , ⊢t)  with amgu A B (_ , σ)
--  ... | nothing       = no  λ where (_ , σ′ , ⊢t′) → ¬switch ⊢t {!!} {!⊢t′!} -- [TODO] A proof-releant unification is needed
--  ... | just (l , σ′) = yes (l , σ′ , ⊢⇉ {!!} {!!})
  inherit Γ A (op x) σ = {!!}
