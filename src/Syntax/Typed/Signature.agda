open import Prelude

module Syntax.Typed.Signature (T : Set) where

open import Syntax.Context T

Fam : (ℓ : Level) → Set (lsuc ℓ)
Fam ℓ = T → Ctx → Set ℓ

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


⟦_⟧ᵃ_ : Args → Fam ℓ → Ctx → Set ℓ
(⟦ ∅            ⟧ᵃ X) _ = ⊤
(⟦ (Δ , A) ∙ as ⟧ᵃ X) Γ = X A (Δ ++ Γ) ×  (⟦ as ⟧ᵃ X) Γ

⟦_⟧_ : Sig O → Fam ℓ → Fam ℓ
(⟦ s ⟧ X) A Γ = Σ[ o ∈ _ ] A ≡ sort s o × (⟦ arity s o ⟧ᵃ X) Γ

mapᵃ : (as : Args) → (f : X ⇒ Y)
  → ⟦ as ⟧ᵃ X ⇒₁ ⟦ as ⟧ᵃ Y
mapᵃ ∅         _ _      = _
mapᵃ (a ∙ as) f (x , y) = f x , mapᵃ as f y

map : (s : Sig O) → (f : X ⇒ Y)
  → ⟦ s ⟧ X ⇒ ⟦ s ⟧ Y
map s f (o , refl , x) = o , refl , mapᵃ (arity s o) f x

record _-Alg (s : Sig O) (X : Fam ℓ) : Set ℓ where
  field
    var : _∈_     ⇒ X
    alg : ⟦ s ⟧ X ⇒ X
open _-Alg public