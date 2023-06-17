{-# OPTIONS #-}

open import Prelude
  hiding (lookup; _⟨_⟩_)

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

import      Syntax.BiTyped.Raw.Functor           SD Id as R
open import Syntax.BiTyped.Raw.Term                 Id D
  hiding (Raw⇐; Raw⇒; Raw)
  renaming (_⦂_ to infix 4 _⦂_; Raw⇐₀ to Raw⇐; Raw⇒₀ to Raw⇒; Raw₀ to Raw)
open import Syntax.BiTyped.Extrinsic.Functor     SD Id
open import Syntax.BiTyped.Extrinsic.Term           Id D

open import Theory.ModeCorrectness.UniqueSynthesised Id D mc

open MC SD
module MCF = Functor Id
open B SD

private variable
  d   : Mode
  Ξ Θ : ℕ
  A B : TExp Θ
  As  : TExps Θ
  xs  : Fins Ξ
  Γ   : Cxt
  ρ   : TSub Ξ Θ
  t u : Raw d

postulate
  amgu : {xs : Fins Ξ} (t : TExp Ξ) (u : TExp Θ) (ρ : Sub⊆ xs Θ)
    → MinDec (Ext ρ λ {ys} ρ′ → Σ (fv t ⊆ ys) λ p → sub⊆ ρ′ t p ≡ u)

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
    → Dec (⟦ D ⟧ᶜ ⊢⇆ Chk A Γ t)
  checkᶜ (ι Chk A Ds) refl mc Γ t A₀ = {!!}

  -- Finish synthesise first 
  synthesiseᶜ
    : (D : ConD) → ConD.mode D ≡ Syn → ModeCorrectᶜ D
    → (Γ : Cxt) (t : R.⟦ D ⟧ᶜ Raw Syn)
    → Dec (∃[ A ] ⟦ D ⟧ᶜ ⊢⇆ Syn A Γ t)
  synthesiseᶜ (ι {Ξ} Syn A Ds) refl (Ds⊆Ξ , SDs , A⊆Ds) Γ (refl , ts)  with synthesiseⁿ Ds SDs Γ ts none
  ... | noₘ ¬∃σ     = no (λ where
    (A , ρ , refl , ⊢t) → {!!})
  ... | yesₘ ys ρ ((none⊑ρ , Ds⊆ys , ⊢ts) , minPρ) = let ρ′ = (toSub (Ds⊆ys ∘ Ds⊆Ξ) ρ) in
    yes (A ⟨ ρ′ ⟩ , ρ′ , refl , {!⊢ts!})

  synthesiseⁿ
    : (Ds : ArgsD Ξ) (mc : ModeCorrectᵃˢ [] Ds)
    → (Γ  : Cxt) (ts : R.⟦ Ds ⟧ᵃˢ Raw)
    → {xs : Fins Ξ} (ρ : Sub⊆₀ xs)
    → MinDec
        (Ext ρ λ {ys} ρ′ → Σ (known Ds ⊆ ys) λ p → MCF.⟦ Ds ⟧⇒ᵃˢ ys p mc Raw ⊢⇆ ρ′ Γ ts)
  synthesiseⁿ []                _  _ _  ρ =
    yesₘ _ ρ (((⊑-refl ρ) , ((λ ()) , tt)) , λ σ (ρ⊑σ , _) → ρ⊑σ)

  synthesiseⁿ (Δ ⊢[ Chk ] A ∷ Ds) (Δ⊆ , mcⁿ) Γ (t , ts) ρ with synthesiseⁿ Ds mcⁿ Γ ts ρ
  ... | noₘ ¬∃σ   = noₘ λ where
    σ (ρ⊑σ , Ds⊆zs , ⊢t , ⊢ts) → ¬∃σ σ (ρ⊑σ , Ds⊆zs , ⊢ts)
  ... | yesₘ ys ρ′ ((ρ⊑ρ′ , Ds⊆ys , ⊢ts) , Minρ′) with
    checkᵃ Δ ys (Ds⊆ys ∘ Δ⊆ ∘ L.++⁺ʳ _) ρ′ Γ t (sub⊆ ρ′ A (Ds⊆ys ∘ Δ⊆ ∘ L.++⁺ˡ))
  ... | no ¬⊢t = noₘ {!!}
  ... | yes ⊢t = yesₘ ys ρ′ ((ρ⊑ρ′ , Ds⊆ys , ⊢t , ⊢ts) ,
    (λ {zs} σ (ρ⊑σ , Ds⊆zs , Pσ) → Minρ′ σ (ρ⊑σ , Ds⊆zs , (Pσ .proj₂))))

  synthesiseⁿ (Δ ⊢[ Syn ] A ∷ Ds) (Δ⊆ , mcⁿ) Γ (t , ts) ρ with synthesiseⁿ Ds mcⁿ Γ ts ρ
  ... | noₘ ¬∃σ   = noₘ λ where
    σ (ρ⊑σ , Ds⊆zs , ⊢t , ⊢ts) → ¬∃σ σ (ρ⊑σ , Ds⊆zs ∘ L.++⁺ʳ _ , ⊢ts)
  ... | yesₘ ys ρ′ ((ρ⊑ρ′ , Ds⊆ys , ⊢ts) , Minρ′) with
    synthesiseᵃ Δ ys (Ds⊆ys ∘ Δ⊆) ρ′ Γ t
  ... | no ¬⊢t = noₘ {!!}
  ... | yes (B , ⊢t) with amgu A B ρ′
  ... | noₘ       A≠B     = {!!}
  ... | yesₘ zs γ MinAγ=B = {!!} -- yesₘ zs γ (({!!} , {!!}) , {!!}) 
  
  synthesiseᵃ
    : (Δ : TExps Ξ) (xs : Fins Ξ) (Δ⊆ : Cover xs Δ) (ρ : Sub⊆₀ xs)
    → (Γ : Cxt) (t : R.⟦ Δ ⟧ᵃ (Raw⇒))
    → Dec (∃[ A ] MCF.⟦ Δ ⟧ᵃ xs Δ⊆ Raw (_⊢_⇒ A) ρ Γ t)
  synthesiseᵃ []      As Δ⊆ ρ Γ t       = synthesise Γ t
  synthesiseᵃ (A ∷ Δ) As Δ⊆ ρ Γ (x , t) =
    synthesiseᵃ Δ As (Δ⊆ ∘ L.++⁺ʳ _) ρ (x ⦂ sub⊆ ρ A (Δ⊆ ∘ L.++⁺ˡ) , Γ) t

  checkᵃ
    : (Δ : TExps Ξ) (xs : Fins Ξ) (Δ⊆ : Cover xs Δ) (ρ : Sub⊆₀ xs)
    → (Γ : Cxt) (t : R.⟦ Δ ⟧ᵃ (Raw⇐)) (A : Ty)
    → Dec (MCF.⟦ Δ ⟧ᵃ xs Δ⊆ Raw (_⊢_⇐ A) ρ Γ t)
  checkᵃ []      xs Δ⊆ ρ Γ t       A₀ = check Γ t A₀
  checkᵃ (A ∷ Δ) xs Δ⊆ ρ Γ (x , t) A₀ = 
    checkᵃ Δ xs (Δ⊆ ∘ L.++⁺ʳ _) ρ (x ⦂ sub⊆ ρ A (Δ⊆ ∘ L.++⁺ˡ) , Γ) t A₀
