open import Prelude

module Syntax.Typed.Signature (T : Set) where

open import Syntax.Typed.Context T

Arg  = List T × T
Args = List Arg

private variable
  O   : Set
  A B : T
  Γ   : Ctx
  X Y : Fam ℓ

record Sig (O : Set) : Set where
  constructor sig
  field ∣_∣ : O → Args × T

  arity = proj₁ ∘ ∣_∣
  sort  = proj₂ ∘ ∣_∣
open Sig public

⟦_⟧ᵇ_ : Arg → Fam ℓ → Ctx → Set ℓ
(⟦ ∅       , A ⟧ᵇ X) Γ = X A Γ
(⟦ (B ∙ Δ) , A ⟧ᵇ X) Γ = (⟦ Δ , A ⟧ᵇ X) (B ∙ Γ)

⟦_⟧ᵃ_ : Args → Fam ℓ → Ctx → Set ℓ
(⟦ ∅      ⟧ᵃ X) _ = ⊤
(⟦ a ∙ as ⟧ᵃ X) Γ = (⟦ a ⟧ᵇ X) Γ ×  (⟦ as ⟧ᵃ X) Γ

⟦_⟧_ : Sig O → Fam ℓ → Fam ℓ
(⟦ s ⟧ X) A Γ = Σ[ o ∈ _ ] A ≡ sort s o × (⟦ arity s o ⟧ᵃ X) Γ

mapᵇ : (a : Arg) → (f : X ⇒ Y)
  → ⟦ a ⟧ᵇ X ⇒₁ ⟦ a ⟧ᵇ Y
mapᵇ (∅     , A) f t = f t
mapᵇ (B ∙ Δ , A) f t = mapᵇ (Δ , A) f t

mapᵃ : (as : Args) → (f : X ⇒ Y)
  → ⟦ as ⟧ᵃ X ⇒₁ ⟦ as ⟧ᵃ Y
mapᵃ ∅         _ _      = _
mapᵃ (a ∙ as) f (x , y) = mapᵇ a f x , mapᵃ as f y

map : (s : Sig O) → (f : X ⇒ Y)
  → ⟦ s ⟧ X ⇒ ⟦ s ⟧ Y
map s f (o , refl , x) = o , refl , mapᵃ (arity s o) f x

record _-Alg (s : Sig O) (X : Fam ℓ) : Set ℓ where
  field
    var : _∈_     ⇒ X
    alg : ⟦ s ⟧ X ⇒ X
open _-Alg public