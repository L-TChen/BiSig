{-# OPTIONS #-}

open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

import Theory.ModeCorrectness.Description as MC

module Theory.ModeCorrectness.Synthesis {SD : S.Desc}
  (Id : Set) ⦃ decEqId : DecEq Id ⦄
  (D : B.Desc SD) (mc : MC.ModeCorrect SD D) where

import Data.List.Relation.Unary.All as All

open import Syntax.NamedContext           SD Id
  hiding (Cxt)
  renaming (Cxt₀ to Cxt)
open import Syntax.NamedContext.Decidable    Id

open import Syntax.Simple SD

import      Syntax.BiTyped.Raw.Functor            SD Id as R
open import Syntax.BiTyped.Raw.Term                  Id D
  hiding (Raw⇐; Raw⇒; Raw)
  renaming (_⦂_ to infix 4 _⦂_; Raw⇐₀ to Raw⇐; Raw⇒₀ to Raw⇒; Raw₀ to Raw)
open import Syntax.BiTyped.Extrinsic.Functor      SD Id
open import Syntax.BiTyped.Extrinsic.Term            Id D

open import Theory.ModeCorrectness.UniqueSynthesised Id D mc

open import Theory.ModeCorrectness.Functor        SD Id as M
open import Theory.ModeCorrectness.Properties        Id D mc

open MC SD
open B SD
open ≡-Reasoning

private variable
  d   : Mode
  Ξ Θ : ℕ
  A B : TExp Θ
  As  : TExps Θ
  xs ys : Fins# Ξ
  Γ   : Cxt
  ρ   : TSub Ξ Θ
  t u : Raw d

module _ where mutual
  synthesise
    : (Γ : Cxt) (t : Raw⇒)
    → Dec (∃[ A ] Γ ⊢ t ⇒ A)

  check
    : (Γ : Cxt) (t : Raw⇐) (A : Ty)
    → Dec (Γ ⊢ t ⇐ A)

  synthesise Γ (` x)   with lookup Γ x
  ... | no  x∉       = no λ where (A , ⊢` x∈) → x∉ (A , x∈)
  ... | yes (A , x∈) = yes (A , ⊢` x∈)

  synthesise Γ (t ⦂ A) with check Γ t A
  ... | no  ⊬t = no λ where (A , ⊢⦂ ⊢t) → ⊬t ⊢t
  ... | yes ⊢t = yes (A , ⊢⦂ ⊢t)

  synthesise Γ (op (i , t@(eq , _))) with synthesiseᶜ (Desc.rules D i) eq (mc i) Γ t
  ... | no ⊬t  = no λ where (A , ⊢op _ ⊢t) → ⊬t (A , ⊢t)
  ... | yes (A , ⊢t) = yes (A , ⊢op _ ⊢t)

  check Γ (t ↑)  A with synthesise Γ t
  ... | no  ⊬t = no λ where (⊢↑ refl ⊢t) → ⊬t (A , ⊢t)
  ... | yes (B , ⊢t) with A ≟ B
  ... | no ¬A=B = no (¬switch ⊢t ¬A=B)
  ... | yes A=B = yes (⊢↑ A=B ⊢t)

  check Γ (op (i , t@(eq , _))) A with checkᶜ (Desc.rules D i) eq (mc i) Γ t A
  ... | no  ⊬t = no (λ where (⊢op _ ⊢t) → ⊬t ⊢t)
  ... | yes ⊢t = yes (⊢op _ ⊢t)

  checkᶜ
    : (D : ConD) → ConD.mode D ≡ Chk → ModeCorrectᶜ D
    → (Γ : Cxt) (t : R.⟦ D ⟧ᶜ Raw Chk) (A : Ty)
    → Dec (⟦ D ⟧ᶜ ⊢⇔ Chk A Γ t)
  checkᶜ (ι Chk A Ds) refl mc Γ t A₀ = {!!}

  -- Finish synthesise first 
  synthesiseᶜ
    : (D : ConD) → ConD.mode D ≡ Syn → ModeCorrectᶜ D
    → (Γ : Cxt) (t : R.⟦ D ⟧ᶜ Raw Syn)
    → Dec (∃[ A ] ⟦ D ⟧ᶜ ⊢⇔ Syn A Γ t)
  synthesiseᶜ (ι Syn A Ds) refl (Ds⊆Ξ , SDs , A⊆Ds) Γ (refl , ts)
    with synthesiseⁿ Ds SDs Γ ts empty (λ ())
  ... | yesₘ ρ Pρ = yes {!!}
  ... | noₘ   ¬Pσ = no  {!!}

  synthesiseⁿ
    : (Ds : ArgsD Ξ) (mc : ModeCorrectᵃˢ ys Ds)
    → (Γ  : Cxt) (ts : R.⟦ Ds ⟧ᵃˢ Raw)
    → ((xs , ρ) : ∃Sub⊆ Ξ) (ys⊆ : ys #⊆ xs)
    → MinDec (Ext (_ , ρ) λ ρ̅ →
        Σ[ Ds⊆ ∈ ys ∪ known Ds #⊆ _ ] M.⟦ Ds ⟧ᵃˢ ρ̅ ys Ds⊆ mc Raw ⊢⇔ Γ ts)

  synthesiseⁿ []       _        _ _        ρ ys⊆ = yesₘ ρ (Pρ→MinExtP (ys⊆ ∘ ∪-⊆⁺ #⊆-refl []⊆xs , _))

  synthesiseⁿ {ys = ys} (Δ ⊢[ Syn ] Aₙ ∷ Ds) (Δ⊆Ds , mc) Γ (t , ts) ρ ys⊆ with synthesiseⁿ Ds mc Γ ts ρ ys⊆

  ... | noₘ ¬∃σ = noₘ λ where
    σ (ext-con ρ≤σ (Ds⊆ , ⊢t , ⊢ts)) → ¬∃σ σ (ext-con ρ≤σ (Ds⊆ ∘ ∪-monotoneʳ ys (∪⁺ʳ (vars Aₙ)) , ⊢ts))

  ... | yesₘ (ys′ , ρ̅) (min-con (ext-con ρ≤ρ̅ (Ds⊆ , ⊢ts)) minρ̅)
    with synthesiseᵃ Δ (_ , ρ̅) (All.map (λ {B} B⊆ {x} x∈ → Ds⊆ (B⊆ x∈)) Δ⊆Ds) Γ t
  ... | no  ¬⊢t = noₘ λ where
    (zs , σ) (ext-con ρ≤σ (Ds⊆′ , ⊢t , ⊢ts)) →
      let ρ̅≤σ = minρ̅ (_ , σ) (ext-con ρ≤σ (Ds⊆′ ∘ ∪-monotoneʳ ys (∪⁺ʳ (vars Aₙ)) , ⊢ts)) in
      ¬⊢t (sub⊆ σ Aₙ (Ds⊆′ ∘ λ x∈ → ∪⁺ʳ ys (∪⁺ˡ x∈)) , ρ≤σ→⊢tᵃ ρ̅≤σ Δ t ⊢t)

  ... | yes (A , ⊢t) with acmp Aₙ A (_ , ρ̅)

  ... | noₘ ¬Aₙ≈A  = noₘ λ where
    (zs , σ) (ext-con ρ≤σ (Ds⊆′ , ⊢t′ , ⊢ts′)) →
      let ρ̅≤σ = minρ̅ (_ , σ) (ext-con ρ≤σ (Ds⊆′ ∘ ∪-monotoneʳ ys (∪⁺ʳ (vars Aₙ)) , ⊢ts′))
      in ¬Aₙ≈A (_ , σ) (ext-con (minρ̅ (_ , σ) record
        { ext     = ≤-trans ρ≤ρ̅ ρ̅≤σ
        ; witness = (Ds⊆′ ∘ ∪-monotoneʳ ys (∪⁺ʳ (vars Aₙ))) , ⊢ts′
        }) (_ , sym (uniqᵐ-↑ Δ ρ̅≤σ ⊢t ⊢t′)))

  ... | yesₘ (zs , σ) (min-con (ext-con ρ̅≤σ@(≤-con ys⊆zs _) (Aₙ⊆ , refl)) minσ) = yesₘ (_ , σ) (record
    { proof      = record
      { ext     = ≤-trans ρ≤ρ̅ ρ̅≤σ
      ; witness =  ∪-⊆⁺ {xs = ys} ((ys⊆zs ∘ ρ≤ρ̅ .domain-ext) ∘ ys⊆) (∪-⊆⁺ Aₙ⊆ (ys⊆zs ∘ Ds⊆ ∘ ∪⁺ʳ ys))  , subst (λ A →
        M.⟦ Δ ⟧ᵃ (_ , σ) (L.A.map (λ {A} A⊆ {x} x∈ → _ ) Δ⊆Ds) Raw (⊢⇔ Syn A) Γ t) (sub⊆-⊆-irrelevant σ Aₙ _ _) (ρ≤σ→⊢tᵃ′ ρ̅≤σ Δ t ⊢t) ,
        ρ≤σ→⊢tⁿ′ ρ̅≤σ  Ds ys mc _ _ ts ⊢ts
      }
    ; minimality = λ where
      (zs′ , γ) (ext-con ρ≤γ (Ds⊆′ , ⊢t′ , ⊢ts′)) →
        let ρ̅≤γ = minρ̅ (_ , γ) (ext-con ρ≤γ (Ds⊆′ ∘ ∪-monotoneʳ ys (∪⁺ʳ (vars Aₙ)) , ⊢ts′)) in
        minσ (_ , γ) record 
        { ext     = ρ̅≤γ
        ; witness = Ds⊆′ ∘ ∪⁺ʳ ys ∘ ∪⁺ˡ , sym (uniqᵐ-↑ Δ ρ̅≤γ ⊢t ⊢t′)
        } 
    })

  synthesiseⁿ (Δ ⊢[ Chk ] Aₙ ∷ Ds) (A⊆Ds ∷ Δ⊆Ds , mc) Γ (t , ts) ρ ys⊆ with synthesiseⁿ Ds mc Γ ts ρ ys⊆

  ... | noₘ ¬∃σ = noₘ λ where
    σ (ext-con ρ≤σ (Ds⊆ , ⊢t , ⊢ts)) → ¬∃σ σ (ext-con ρ≤σ (Ds⊆ , ⊢ts))

  ... | yesₘ (xs , ρ̅) (min-con (ext-con ρ≤ρ̅ (Ds⊆ , ⊢ts)) minρ̅)
    with checkᵃ Δ (xs , ρ̅) (L.A.map (λ {B} B⊆ {x} x∈ → Ds⊆ (B⊆ x∈)) Δ⊆Ds) Γ t (sub⊆ ρ̅ Aₙ (Ds⊆ ∘ A⊆Ds))

  ... | no  ¬⊢t = noₘ λ where
    (zs , σ) (ext-con ρ̅≤σ (Ds⊆′ , ⊢t′ , ⊢ts′)) →
      let ρ̅≤σ = minρ̅ (_ , σ) (ext-con ρ̅≤σ (Ds⊆′ , ⊢ts′))
          eq : sub⊆ σ Aₙ (λ x → Ds⊆′ (A⊆Ds x)) ≡ sub⊆ ρ̅ Aₙ (λ x → Ds⊆ (A⊆Ds x))
          eq = begin
            sub⊆ σ Aₙ (λ x → Ds⊆′ (A⊆Ds x))
              ≡⟨ ρ=σ→subρ=subσ Aₙ σ ρ̅ (Ds⊆′ ∘ A⊆Ds) (Ds⊆ ∘ A⊆Ds)
                (λ x∈ → begin
                  σ (Ds⊆′ (A⊆Ds x∈))
                    ≡⟨ cong σ (#∈-uniq _ _) ⟩
                  σ _
                    ≡⟨ sym (ρ̅≤σ .consistency (Ds⊆ (A⊆Ds x∈))) ⟩
                  ρ̅ (Ds⊆ (A⊆Ds x∈))
                    ∎) ⟩
            sub⊆ ρ̅ Aₙ _
              ≡⟨ sub⊆-⊆-irrelevant ρ̅ Aₙ _ _ ⟩
            sub⊆ ρ̅ Aₙ (λ x → Ds⊆ (A⊆Ds x))
              ∎
      in
      ¬⊢t (ρ≤σ→⊢tᵃ ρ̅≤σ Δ t (subst (λ A → M.⟦ Δ ⟧ᵃ (_ , σ) _ Raw (⊢⇔ Chk A) Γ t) eq ⊢t′))

  ... | yes ⊢t = yesₘ (_ , ρ̅) (min-con (ext-con ρ≤ρ̅ (Ds⊆ , ⊢t , ⊢ts))
    λ σ (ext-con ρ≤σ (Ds⊆′ , ⊢t , ⊢ts)) → minρ̅ σ (ext-con ρ≤σ (Ds⊆′ , ⊢ts)))
    
  synthesiseᵃ
    : (Δ : TExps Ξ) ((xs , ρ) : ∃Sub⊆ Ξ) (Δ⊆ : Cover xs Δ)
    → (Γ : Cxt) (t : R.⟦ Δ ⟧ᵃ (Raw⇒))
    → Dec (∃[ A ] M.⟦ Δ ⟧ᵃ (_ , ρ) Δ⊆ Raw (_⊢_⇒ A) Γ t)
  synthesiseᵃ []      (_ , ρ) Δ⊆        Γ t       = synthesise Γ t
  synthesiseᵃ (A ∷ Δ) (_ , ρ) (A⊆ ∷ Δ⊆) Γ (x , t) =
    synthesiseᵃ Δ (_ , ρ) (Δ⊆) (x ⦂ sub⊆ ρ A (A⊆) , Γ) t

  checkᵃ
    : (Δ : TExps Ξ) ((xs , ρ) : ∃Sub⊆ Ξ) (Δ⊆ : Cover xs Δ)
    → (Γ : Cxt) (t : R.⟦ Δ ⟧ᵃ (Raw⇐)) (A : Ty)
    → Dec (M.⟦ Δ ⟧ᵃ (_ , ρ) Δ⊆ Raw (_⊢_⇐ A) Γ t)
  checkᵃ []      (_ , ρ) Δ⊆        Γ t       A₀ = check Γ t A₀
  checkᵃ (A ∷ Δ) (_ , ρ) (A⊆ ∷ Δ⊆) Γ (x , t) A₀ = 
    checkᵃ Δ (_ , ρ) Δ⊆ (x ⦂ sub⊆ ρ A A⊆ , Γ) t A₀
