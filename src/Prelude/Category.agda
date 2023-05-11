{-# OPTIONS --safe #-}

module Prelude.Category where

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Level
open import Function
  hiding (id)

open ≡-Reasoning

private variable
  a b c : Level

record IsCategory (Obj : Set) (Mor : Obj → Obj → Set) : Set where
  infixl 5 _⨟_
  field
    id      : {C     : Obj} → Mor C C
    _⨟_     : {C D E : Obj} → Mor C D → Mor D E → Mor C E
    
    ⨟-idᵣ   : {C D   : Obj}
      → (f : Mor C D)
      → f ⨟ id ≡ f

    ⨟-idₗ   : {C D   : Obj}
      → (f : Mor C D)
      → id ⨟ f ≡ f

    ⨟-assoc : {C D E F : Obj}
      → (f : Mor C D) (g : Mor D E) (h : Mor E F)
      → (f ⨟ g) ⨟ h ≡ f ⨟ (g ⨟ h)

  private variable
    C D E : Obj

  infix 4 _⊒_ _⊑_
  _⊒_ _⊑_
    : {C D E : Obj}
    → Mor C D → Mor C E → Set
  _⊒_ {C} {D} {E} f g = Σ[ h ∈ Mor E D ] f ≡ g ⨟ h

  _⊑_ f g = g ⊒ f

  𝐘 : Obj → Set₁
  𝐘 C = {D : Obj} → Mor C D → Set

  infixl 8 _[_⨟_]
  _[_⨟_]
    : (P : 𝐘 C) (f : Mor C D)
    → 𝐘 D
  P [ f ⨟ g ] = P (f ⨟ g)

  -- ???
  Min : 𝐘 C → 𝐘 C
  Min {C} P f = P f ×
    (∀ {D} (g : Mor C D) → P g → g ⊒ f)

  ∃ₘ : 𝐘 C → Set
  ∃ₘ {C} P = ∃₂ λ (D : Obj) (f : Mor C D) → P f 

  infix 2 ∃ₘ
  syntax ∃ₘ (λ x → P) = ∃ₘ[ x ] P

open IsCategory ⦃...⦄ public
  
record Category : Set₁ where
  field
    Obj        : Set
    Mor        : Obj → Obj → Set
    isCategory : IsCategory Obj Mor
open Category

record Functor
  {Obj₁ : Set} {Mor₁ : Obj₁ → Obj₁ → Set} ⦃ isCat₁ : IsCategory Obj₁ Mor₁ ⦄ 
  {Obj₂ : Set} {Mor₂ : Obj₂ → Obj₂ → Set} ⦃ isCat₂ : IsCategory Obj₂ Mor₂ ⦄ 
  (Fₒ : Obj₁ → Obj₂)  : Set where
  field
    Fₘ  : {A B : Obj₁}
      → Mor₁ A B → Mor₂ (Fₒ A) (Fₒ B)
    Fₘ-id : {A : Obj₁} → Fₘ {A} id ≡ id
    Fₘ-⨟  : {A B C : Obj₁}
      → (f : Mor₁ A B) (g : Mor₁ B C)
      → Fₘ (f ⨟ g) ≡ Fₘ f ⨟ Fₘ g
open Functor ⦃...⦄ public

record IsPresheaf {Obj : Set} {Mor : Obj → Obj → Set}
  ⦃ isCat : IsCategory Obj Mor ⦄ (F : Obj → Set) : Set where
  infixl 8 _⟨_⟩
  field
    _⟨_⟩ : {C D : Obj}
      → F C → Mor C D → F D

    ⟨⟩-id : {C : Obj}
      → (x : F C)
      → x ⟨ id ⟩ ≡ x

    ⟨⟩-⨟ : {C D E : Obj}
      → (f  : Mor C D) (g : Mor D E)
      → (x : F C) 
      → x ⟨ f ⨟ g ⟩ ≡ x ⟨ f ⟩ ⟨ g ⟩
open IsPresheaf ⦃...⦄ public

module _ {Obj : Set} {Mor : Obj → Obj → Set} {Tm : Obj → Set}
  ⦃ _ : IsCategory Obj Mor ⦄ ⦃ _ : IsPresheaf Tm ⦄ where
  infix 4 _≈_by_

  private variable
    A B C : Obj

  _≈_by_
    : (t u : Tm A) → 𝐘 A
  t ≈ u by σ = t ⟨ σ ⟩ ≡ u ⟨ σ ⟩

  Unifies-sym
    : (t u : Tm A) (σ : Mor A B)
    → t ≈ u by σ → u ≈ t by σ
  Unifies-sym t u σ eq = sym eq

  unifies-⨟
    : (σ : Mor A B) (ρ : Mor B C)
    → (t u : Tm A)
    → t ≈ u by σ
    → t ≈ u by σ ⨟ ρ
  unifies-⨟ σ ρ t u eq = begin
    t ⟨ σ ⨟ ρ ⟩
      ≡⟨ ⟨⟩-⨟ _ _ t ⟩
    t ⟨ σ ⟩ ⟨ ρ ⟩
      ≡⟨ cong _⟨ ρ ⟩ eq ⟩
    u ⟨ σ ⟩ ⟨ ρ ⟩
      ≡⟨ sym $ ⟨⟩-⨟ _ _ u ⟩
    u ⟨ σ ⨟ ρ ⟩
      ∎

  id-minimal
    : (σ : Mor A B)
    → (t : Tm A)
    → Min {Obj} (λ ρ → t ≈ t by σ ⨟ ρ) id
  id-minimal σ t = refl , λ g eq → g , (begin
    g
      ≡⟨ sym (⨟-idₗ g) ⟩
    id ⨟ g
      ∎)
{-
module _
  {Obj₁ : Set} {Mor₁ : Obj₁ → Obj₁ → Set} ⦃ isCat₁ : IsCategory Obj₁ Mor₁ ⦄ 
  {Obj₂ : Set} {Mor₂ : Obj₂ → Obj₂ → Set} ⦃ isCat₂ : IsCategory Obj₂ Mor₂ ⦄ 
  {Fₒ : Obj₁ → Obj₂} ⦃ func : Functor Fₒ ⦄
  (P : Obj₂ → Set)
  ⦃ isPresheaf : IsPresheaf P ⦄ where

  presheaf∘functor : IsPresheaf λ C → P (Fₒ C)
  presheaf∘functor ._⟨_⟩  x f = x ⟨ Fₘ f ⟩
  presheaf∘functor .⟨⟩-id {C} x = begin
    x ⟨ Fₘ id ⟩
      ≡⟨ cong (x ⟨_⟩) Fₘ-id ⟩
    x ⟨ id ⟩
      ≡⟨ ⟨⟩-id _ ⟩
    x
      ∎
  presheaf∘functor .⟨⟩-⨟ f g x  = begin
    x ⟨ Fₘ (f ⨟ g) ⟩
      ≡⟨ cong (x ⟨_⟩) (Fₘ-⨟ f g) ⟩
    x ⟨ Fₘ f ⨟ Fₘ g ⟩
      ≡⟨ ⟨⟩-⨟ (Fₘ f) (Fₘ g) x ⟩
    x ⟨ Fₘ f ⟩ ⟨ Fₘ g ⟩
      ∎
-}
