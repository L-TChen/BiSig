module Prelude where

open import Agda.Primitive public
  using (_⊔_)
  renaming (lzero to 𝓤₀
          ; Level to Universe
          ; Setω to 𝓤ω
          ; Set to Type
          )

open import Agda.Primitive.Cubical public
  hiding (I)

open import Cubical.Foundations.Function     public
  using (_∘_)

import Cubical.Foundations.Prelude as CubicalPrelude 
open CubicalPrelude                          public
  hiding (Sub; _∎; _▷_; _◁_; I)
  renaming (funExt⁻ to cong-app; subst2 to subst₂)
open import Cubical.HITs.PropositionalTruncation public
  using (∥_∥; ∣_∣; squash)

open import Cubical.Data.Empty               public
  using (⊥)
  renaming (elim to ⊥-elim)
open import Cubical.Data.Unit                public
  renaming (Unit to ⊤)
open import Cubical.Data.Bool                public
  using (Bool; true; false; _and_; _or_; not)
open import Cubical.Data.Sum                 public
  using (_⊎_; inl; inr)
open import Cubical.Data.Nat                 public
  using (ℕ; suc; zero)
open import Cubical.Data.Nat.Order.Recursive public
  using (_≤?_)
open import Cubical.Data.Sigma               public
  using (Σ; Σ-syntax; ∃-syntax; _×_; _,_)
  renaming (fst to proj₁; snd to proj₂)
open import Cubical.Relation.Nullary         public
  using (¬_; Dec; yes; no)

variable
  𝓤 𝓥 𝓦 𝓣 𝓤' 𝓥' 𝓦' 𝓣' : Universe
  
infix  1 _̇

_̇ : (𝓤 : Universe) → _
𝓤 ̇ = Type 𝓤

universe-of : {𝓤 : Universe} → (X : 𝓤 ̇) → Universe
universe-of {𝓤} X = 𝓤

module ≡-Reasoning where
  open CubicalPrelude public
    using (_≡⟨_⟩_; _∎) 

  infix 1 begin_
  begin_ : {A : 𝓤 ̇} {x y : A}
    → x ≡ y → x ≡ y
  begin_ r = r

PathP-syntax = PathP

infix 4 PathP-syntax
syntax PathP-syntax (λ _ → A) x y = x ≡ y ⦂ A

trans : {A : 𝓤 ̇} {x y z : A}
  → x ≡ y → y ≡ z → x ≡ z
trans p q = p ∙ q

[_,_] : ∀ {a b c} {A : Type a} {B : Type b} {C : A ⊎ B → Type c} →
        ((x : A) → C (inl x)) → ((x : B) → C (inr x)) →
        ((x : A ⊎ B) → C x)
[ f , g ] (inl x) = f x
[ f , g ] (inr y) = g y

id : ∀ {a} {A : Type a} → A → A
id x = x
