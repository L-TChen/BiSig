{-# OPTIONS --safe #-}

module Prelude.Category where

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Level

private variable
  a b c : Level

record IsCategory (Obj : Set a) (Mor : Obj → Obj → Set b) : Set (a ⊔ b) where
  infixl 5 _⨟_
  field
    id      : {C     : Obj} → Mor C C
    _⨟_     : {C D E : Obj} → Mor C D → Mor D E → Mor C E
    
{-
    ⨟-assoc
      : {C D E F : Obj}
      → (f : Mor C D) (g : Mor D E) (h : Mor E F)
      → f ⨟ g ⨟ h ≡ f ⨟ (g ⨟ h)
    ⨟-idₗ
      : {C D : Obj}
      → (f : Mor C D)
      → id ⨟ f ≡ f
    ⨟-idᵣ
      : {C D : Obj}
      → (f : Mor C D)
      → f ⨟ id ≡ f
-}
  _⊑_
    : {C D E : Obj}
    → Mor C D → Mor C E → Set b
  _⊑_ {C} {D} {E} ρ σ = Σ[ ρ′ ∈ Mor E D ] ρ ≡ σ ⨟ ρ′
open IsCategory ⦃...⦄ public
  
record Category {a b} : Set (suc (a ⊔ b)) where
  field
    Obj        : Set a
    Mor        : Obj → Obj → Set b
    isCategory : IsCategory Obj Mor
open Category

record IsPresheaf {Obj : Set a} {Mor : Obj → Obj → Set b}
  (⦃ isCat ⦄ : IsCategory Obj Mor) (F : Obj → Set c) : Set (a ⊔ b ⊔ c) where
  infixl 8 _⟨_⟩
  field
    _⟨_⟩ : {C D : Obj}
      → F C → Mor C D → F D
{-
    ⟨⟩-id : {C : Obj}
      → (t : F C)
      → t ⟨ id ⟩ ≡ t
    ⟨⟩-⨟  : {C D E : Obj}
      → (f : Mor C D) (g : Mor D E)
      → (t : F C)
      → t ⟨ f ⨟ g ⟩ ≡ t ⟨ f ⟩ ⟨ g ⟩
-}

open IsPresheaf ⦃...⦄ public
