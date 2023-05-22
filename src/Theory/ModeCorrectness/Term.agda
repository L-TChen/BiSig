{-# OPTIONS --with-K --rewriting #-}

open import Prelude
  hiding (lookup)

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

import Theory.ModeCorrectness.Description as M

module Theory.ModeCorrectness.Term {SD : S.Desc}
  (Id : Set) (_≟Id_ : (x y : Id) → Dec (x ≡ y))
  (D : B.Desc SD) (mc : M.ModeCorrect SD Id D) where

open M SD Id
open B SD

open import Syntax.Context                SD
  renaming (Cxt to UCxt)
open import Syntax.NamedContext           SD Id
open import Syntax.NamedContext.Decidable _≟Id_

open import Syntax.Simple SD

import      Syntax.BiTyped.Raw.Functor           SD Id as R
open import Syntax.BiTyped.Raw.Term                 Id D
open import Syntax.BiTyped.Extrinsic.Functor     SD Id
open import Syntax.BiTyped.Extrinsic.Term           Id D
open import Syntax.BiTyped.Extrinsic.Properties     Id D

open import Theory.Ontologisation.Context           Id

private variable
  mod   : Mode
  n m l : ℕ
  A B   : TExp n
  xs    : List (Fin n)
  Γ     : Cxt   n
  Ds    : ArgsD n
  AD    : ArgD  n
  σ σ₁ σ₂ ρ γ : TSub n m
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
          → ⟦ ConD.args D ⟧ᵃˢ (Raw m) ⊢⇆ ts Γ rs
          → ⟦ ConD.args D ⟧ᵃˢ (Raw m) ⊢⇆ us Γ rs
          → ConD.type D ⟨ ts ⟩ ≡ ConD.type D ⟨ us ⟩
  uniq-⇉ᶜ {D = D} (C⊆xs , _ , SDs) refl ⊢ts ⊢us =
    ≡-fv _ _ (ConD.type D) λ x → uniq-⇉Map _ SDs ⊢ts ⊢us (C⊆xs x)

  uniq-⇉Map
    : (Ds : ArgsD n)
    → ModeCorrectᵃˢ [] Ds
    → {ts : R.⟦ Ds ⟧ᵃˢ (Raw m)}
    → (⊢ts : ⟦ Ds ⟧ᵃˢ (Raw m) ⊢⇆ σ₁ Γ ts)
    → (⊢us : ⟦ Ds ⟧ᵃˢ (Raw m) ⊢⇆ σ₂ Γ ts)
    → ∀ {x} → x ∈ Known [] Ds
    → V.lookup σ₁ x ≡ V.lookup σ₂ x -- σ₁ x ≡ σ₂ x
  uniq-⇉Map []                    _             _          _         ()
  uniq-⇉Map (_ ⊢[ Check ] _ ∷ Ds) (_ , _ , SDs) (_ , ⊢ts)  (_ , ⊢us) =
    uniq-⇉Map Ds SDs ⊢ts ⊢us
  uniq-⇉Map (Θ ⊢[ Infer ] C ∷ Ds) (SD , SDs)    (⊢t , ⊢ts) (⊢u , ⊢us) i with ∈-++⁻ (fv C) i
  ... | inl j = uniq-⇉Mapᵃ C Θ SD ⊢t ⊢u (uniq-⇉Map Ds SDs ⊢ts ⊢us) j
  ... | inr j = uniq-⇉Map Ds SDs ⊢ts ⊢us j

  uniq-⇉Mapᵃ
    : (C : TExp n) (Θ : TExps n)
    → ModeCorrectᵃ xs Θ
    → {t : R.⟦ Θ ⟧ᵃ (Raw m Infer)}
    → (⊢t : ⟦ Θ ⟧ᵃ (Raw m) (⊢⇆ Infer (C ⟨ σ₁ ⟩)) σ₁ Γ t)
    → (⊢u : ⟦ Θ ⟧ᵃ (Raw m) (⊢⇆ Infer (C ⟨ σ₂ ⟩)) σ₂ Γ t)
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
  → B ≢ A
  → ¬ (Γ ⊢ (t ↑) ⇇ B)
¬switch ⊢t B≠A (⊢⇉ B=A ⊢t′) rewrite uniq-⇉ ⊢t ⊢t′ = B≠A B=A

------------------------------------------------------------------------------
-- A type checker

open import Syntax.Simple.Rewrite SD

module _ {m : ℕ} where mutual
  synthesise
    : (Γ : Cxt m) (t : Raw⇉ m) (σ : AList m n)
    → Maybe (∃₂ λ k (ρ : AList n k)
      → Σ[ A ∈ TExp m ] (Typability A Γ t [ toSub σ ⨟]) _ (toSub ρ))

  inherit
    : (Γ : Cxt m) (t : Raw⇇ m) (σ : AList m n) (A : TExp m)
    → Maybe (∃₂ λ k (ρ : AList n k)
      → (Typability A Γ t [ toSub σ ⨟]) _ (toSub ρ))

  synthesise Γ (` x)   σ with lookup Γ x
  ... | no _         = nothing
  ... | yes (A , x∈) = just (_ , id , A , ⊢` (sub-∈ (toSub σ ⨟ id) x∈))

  synthesise Γ (t ⦂ A) σ with inherit Γ t σ A
  ... | nothing = nothing
  ... | just (n , ρ , ⊢t) = just (_ , ρ , A , ⊢⦂ ⊢t refl)

  synthesise Γ (op (i , eq , ts)) σ = {!!}

  inherit Γ (t ↑) σ A  with synthesise Γ t σ
  ... | nothing = nothing
  ... | just (_ , ρ , B , ⊢t) with amgu⁺ A B (σ ⨟ ρ)
  ... | inr _ = nothing
  ... | inl (_ , γ , A≈B , min) rewrite ⨟-assoc (toSub σ) (toSub ρ) (toSub γ) =
    just (_ , ρ ⨟ γ , ⊢⇉ A≈B
      (⊢⟨σ⟩↑ B Γ t (toSub $ σ ⨟ ρ) (toSub σ ⨟ toSub (ρ ⨟ γ))
        (toSub γ , ⨟-assoc (toSub σ) (toSub ρ) (toSub γ)) ⊢t))

  inherit Γ (op (i , eq , ts)) σ A = {!!}

------------------------------------------------------------------------------
-- A proof-relevant type checker

module _ {m : ℕ} where mutual
  synthetise⁺
    : (Γ : Cxt m) (t : Raw⇉ m) (σ : AList m n)
    → Dec (∃₂ λ l (ρ : AList n l) → Σ[ A ∈ TExp m ]
        (Typability A Γ t [ toSub σ ⨟]) l (toSub ρ) )
  inherit⁺
    : (Γ : Cxt m) (t : Raw⇇ m) (σ : AList m n) (A : TExp m)
    → Dec (∃[ l ] Σ[ ρ ∈ AList n l ]
        (Typability A Γ t [ toSub σ ⨟]) l (toSub ρ))

  synthetise⁺ Γ (` x)   σ with lookup Γ x
  ... | no ¬p        = no λ where
    (l , σ′ , A , ⊢` y) → subst-∈→∈ _ Γ ¬p (_ , y)
  ... | yes (A , x∈) = yes (_ , id , A , ⊢` (sub-∈ (toSub σ ⨟ id) x∈))
  synthetise⁺ Γ (t ⦂ A) σ with inherit⁺ Γ t σ A
  ... | no ¬p = no λ where (n , σ , B , ⊢⦂ ⊢t _) → ¬p (_ , σ , ⊢t)
  ... | yes (n , ρ , ⊢t) = yes (_ , ρ , A , ⊢⦂ ⊢t refl)
  synthetise⁺ Γ (op x)  σ = {!!}

  inherit⁺ Γ (t ↑)  σ A with synthetise⁺ Γ t σ
  ... | no ¬p = no λ where (n , σ′ , ⊢⇉ refl ⊢t) → ¬p (n , σ′ , A , ⊢t)
  ... | yes (l , ρ , B , ⊢t)  with amgu⁺ A B (σ ⨟ ρ)
  ... | inr A≉B                 = no λ where
    (_ , γ , ⊢⇉ refl ⊢t′) → {!!} -- ¬switch {_} {Γ ⟨ {!!} ⟩} {B ⟨ {!!} ⟩} {A ⟨ {!!} ⟩} {!!} {!!} {!!}
  ... | inl (_ , γ , A≈B , min) rewrite ⨟-assoc (toSub σ) (toSub ρ) (toSub γ) =
    yes (_ , ρ ⨟ γ , ⊢⇉ A≈B
      (⊢⟨σ⟩↑ B Γ t (toSub $ σ ⨟ ρ) (toSub σ ⨟ toSub (ρ ⨟ γ))
        (toSub γ , ⨟-assoc (toSub σ) (toSub ρ) (toSub γ)) ⊢t))

  inherit⁺ Γ (op x) σ A = {!!}

