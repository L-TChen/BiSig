{-# OPTIONS #-}

open import Prelude
  hiding (lookup; _⟨_⟩_)

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

import Theory.ModeCorrectness.Description as MC

module Theory.ModeCorrectness.Inference {SD : S.Desc}
  (Id : Set) ⦃ decEqId : DecEq Id ⦄
  (D : B.Desc SD) (mc : MC.ModeCorrect SD D) where

import Data.List.Relation.Unary.All as All

open import Syntax.NamedContext           SD Id
open import Syntax.NamedContext.Decidable    Id

open import Syntax.Simple SD

import      Syntax.BiTyped.Raw.Functor           SD Id as R
open import Syntax.BiTyped.Raw.Term                 Id D
  renaming (_⦂_ to infix 4 _⦂_)
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
  xs  : List (Fin Ξ)
  Γ   : Cxt   Θ
  ρ   : TSub Ξ Θ
  t u : Raw Θ d

module _ where mutual
  synthesise
    : (Γ : Cxt 0) (t : Raw⇒ 0)
    → Dec (∃[ A ] Γ ⊢ t ⇒ A)

  inherit
    : (Γ : Cxt 0) (t : Raw⇐ 0) (A : Ty)
    → Dec (Γ ⊢ t ⇐ A)

  synthesise Γ (` x)   with lookup Γ x
  ... | no  x∉       = no λ where (A , ⊢` x∈) → x∉ (A , x∈)
  ... | yes (A , x∈) = yes (A , ⊢` x∈)

  synthesise Γ (t ⦂ A) with inherit Γ t A
  ... | no  ⊬t = no λ where (A , ⊢⦂ ⊢t) → ⊬t ⊢t
  ... | yes ⊢t = yes (A , ⊢⦂ ⊢t)

  synthesise Γ (op (i , t@(eq , ts))) with synthesiseᶜ (Desc.rules D i) eq (mc i) Γ t
  ... | no ⊬t  = no λ where (A , ⊢op _ ⊢t) → ⊬t (A , ⊢t)
  ... | yes (A , ⊢t) = yes (A , ⊢op _ ⊢t)

  inherit Γ (t ↑)  A with synthesise Γ t
  ... | no  ⊬t = no λ where (⊢↑ refl ⊢t) → ⊬t (A , ⊢t)
  ... | yes (B , ⊢t) with A ≟ B
  ... | no ¬A=B = no (¬switch ⊢t ¬A=B)
  ... | yes A=B = yes (⊢↑ A=B ⊢t)

  inherit Γ (op (i , t@(eq , ts))) A with inheritᶜ (Desc.rules D i) eq (mc i) Γ t A
  ... | no  ⊬t = no (λ where (⊢op _ ⊢t) → ⊬t ⊢t)
  ... | yes ⊢t = yes (⊢op _ ⊢t)

  postulate
    eq? : (A : TExp Ξ) (A₀ : TExp Θ)
      → Dec (Σ[ σ ∈ ∈Sub (fv A) Θ ] ∈sub A σ ≡ A₀)

    consistent? : {xs ys : List (Fin Ξ)}
      → (σ : ∈Sub xs Θ) (γ : ∈Sub ys Θ)
      → Dec (Σ[ ρ ∈ ∈Sub (xs ++ ys) Θ ] (Consistent ρ σ × Consistent ρ γ))

  synthesiseᶜ
    : (D : ConD) → ConD.mode D ≡ Syn → ModeCorrectᶜ D
    → (Γ : Cxt 0) (t : R.⟦ D ⟧ᶜ (Raw 0) Syn)
    → Dec (∃[ A ] ⟦ D ⟧ᶜ ⊢⇆ Syn A Γ t)
  synthesiseᶜ (ι Syn A Ds) refl (SDs , A⊆As) Γ (refl , t) = {!!}

  synthesiseᵃˢ
    : (Ds : ArgsD Ξ) (mc : Syn.ModeCorrectᵃˢ Ds)
    → (Γ : Cxt 0) (ts : R.⟦ Ds ⟧ᵃˢ (Raw 0)) {xs : List (Fin Ξ)} (ρ : ∈Sub₀ xs)
    → Dec (∃[ ys ] Σ[ σ ∈ ∈Sub₀ ys ] ρ ⊑ σ × Σ[ Ds⊆ys ∈ known Ds ⊆ ys ]
        MCF.⟦ Ds ⟧⇒ᵃˢ ys Ds⊆ys mc (Raw 0) ⊢⇆ σ Γ ts)

  synthesiseᵃˢ []                  _         _ _        ρ = yes (_ , ρ , ⊑-refl ρ , (λ ()) , tt)

  synthesiseᵃˢ (Δ ⊢[ Chk ] A ∷ Ds) (Δ⊆Ds , SDs) Γ (t , ts) ρ with synthesiseᵃˢ Ds SDs Γ ts ρ
  ... | no ¬p = no λ where
    (_ , σ , ρ⊑σ , Ds⊆ys , ⊢t , ⊢ts) → ¬p (_ , σ , ρ⊑σ , Ds⊆ys , ⊢ts)
  ... | yes (ys , σ , ρ⊑σ , Ds⊆ys , ⊢ts) with inheritᵃ Δ ys (Ds⊆ys ∘ Δ⊆Ds ∘ L.++⁺ʳ _) σ Γ t (∈sub A (⊆-∈Sub (Ds⊆ys ∘ Δ⊆Ds ∘ L.++⁺ˡ) σ))
  ... | no ¬q = no λ where
    (zs , γ , σ⊑γ , Ds⊆zs , ⊢t , ⊢ts) → ¬q {!⊢t!}
  ... | yes ⊢t = yes (_ , σ , ρ⊑σ , Ds⊆ys , ⊢t , ⊢ts)
  
  synthesiseᵃˢ (Δ ⊢[ Syn ] A ∷ Ds) (Δ⊆ , SDs) Γ (t , ts) ρ with synthesiseᵃˢ Ds SDs Γ ts ρ
  ... | no ¬p = no λ where
    (_ , σ , ρ⊑σ , Ds⊆ys , ⊢t , ⊢ts) → ¬p (_ , σ , ρ⊑σ , (Ds⊆ys ∘ L.++⁺ʳ _) , ⊢ts)
  ... | yes (ys , σ , ρ⊑σ , Ds⊆ys , ⊢ts) with synthesiseᵃ Δ ys (Ds⊆ys ∘ Δ⊆) σ Γ t
  ... | no ¬q         = no λ where
    (zs , σ , ρ⊑σ , Ds⊆ys , ⊢t , ⊢ts) → ¬q (∈sub A (⊆-∈Sub (Ds⊆ys ∘ L.++⁺ˡ) σ) , {!⊢t!})
  ... | yes q         = ?
--  ... | yes (A₀ , ⊢t) with eq? A A₀
--  ... | no A≠A₀        = {!!}
--  ... | yes (γ , A=A₀) with consistent? γ ρ
--  ... | no ¬ρ⊥γ     = no {!!}
--  ... | yes (σ , p) = yes (σ , {!⊢t!} , {!⊢ts!})
  
  inheritᶜ
    : (D : ConD) → ConD.mode D ≡ Chk → ModeCorrectᶜ D
    → (Γ : Cxt 0) (t : R.⟦ D ⟧ᶜ (Raw 0) Chk) (A : Ty)
    → Dec (⟦ D ⟧ᶜ ⊢⇆ Chk A Γ t)
  inheritᶜ (ι Chk A Ds) refl mc Γ t A₀ = {!!}

  synthesiseᵃ
    : (Δ : TExps Ξ) (xs : Fins Ξ) (Δ⊆ : Cover xs Δ) (ρ : ∈Sub₀ xs)
    → (Γ : Cxt 0) (t : R.⟦ Δ ⟧ᵃ (Raw⇒ 0))
    → Dec (∃[ A ] MCF.⟦ Δ ⟧ᵃ xs Δ⊆ (Raw 0) (_⊢_⇒ A) ρ Γ t)
  synthesiseᵃ []      As Δ⊆ ρ Γ t       = synthesise Γ t
  synthesiseᵃ (A ∷ Δ) As Δ⊆ ρ Γ (x , t) =
    synthesiseᵃ Δ As (Δ⊆ ∘ L.++⁺ʳ (fv A)) ρ (x ⦂ ∈sub A (⊆-∈Sub (Δ⊆ ∘ L.++⁺ˡ) ρ) , Γ) t

  inheritᵃ
    : (Δ : TExps Ξ) (xs : Fins Ξ) (Δ⊆ : Cover xs Δ) (ρ : ∈Sub₀ xs)
    → (Γ : Cxt 0) (t : R.⟦ Δ ⟧ᵃ (Raw⇐ 0)) (A : Ty)
    → Dec (MCF.⟦ Δ ⟧ᵃ xs Δ⊆ (Raw 0) (_⊢_⇐ A) ρ Γ t)
  inheritᵃ []      As Δ⊆ ρ Γ t       A₀ = inherit Γ t A₀
  inheritᵃ (A ∷ Δ) As Δ⊆ ρ Γ (x , t) A₀ = 
    inheritᵃ Δ As (Δ⊆ ∘ L.++⁺ʳ (fv A)) ρ (x ⦂ ∈sub A (⊆-∈Sub (Δ⊆ ∘ L.++⁺ˡ) ρ) , Γ) t A₀
