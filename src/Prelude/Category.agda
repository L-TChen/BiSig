{-# OPTIONS --safe #-}

module Prelude.Category where

open import Relation.Binary.PropositionalEquality
  hiding (_≗_)
open import Data.Product
open import Data.Empty
  using (⊥)
open import Level
open import Function using (_$_; _∘_)

open import Prelude.Equivalence

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
  _⊒_ {C} {D} {E} f g = Σ[ h ∈ Mor E D ] g ⨟ h ≡ f

  _⊑_ f g = g ⊒ f

  𝐘 : Obj → Set₁
  𝐘 C = (D : Obj) → Mor C D → Set

  _[_⨟]
    : (P : 𝐘 C) (f : Mor C D) 
    → 𝐘 D
  (P [ f ⨟]) _ g = P _ (f ⨟ g)

  infixl 5 _∧_
  infixl 5 _[_⨟]
  infix  4 _≗_
  _∧_ : (P Q : 𝐘 C) → 𝐘 C
  (P ∧ Q) D f = P D f × Q D f 

  ¬ₘ : 𝐘 C → Set
  ¬ₘ P = ∀ {D} f → P D f → ⊥
  
  Min : 𝐘 C → 𝐘 C
  Min {C} P D f = P D f ×
    (∀ {D} (g : Mor C D) → P D g → f ⊑ g)

  _≗_ : (P Q : 𝐘 C) → Set
  _≗_ {C} P Q = {D : Obj} (f : Mor C D) → P D f ⇔ Q D f

  ≗-sym : {P Q : 𝐘 C}
    → P ≗ Q → Q ≗ P
  ≗-sym = ⇔-sym ∘_

  ≗→⇔ : {P Q : 𝐘 C} → P ≗ Q → ∃₂ P ⇔ ∃₂ Q 
  ≗→⇔ P=Q = record
    { to   = map₂ (map₂ (P=Q _ .to))
    ; from = map₂ (map₂ (P=Q _ .from))
    }
    where open Equivalence

  Min≗
    : {P Q : 𝐘 C}
    → P ≗ Q
    → Min P ≗ Min Q
  Min≗ P=Q f = record
    { to   = λ (Pf , min) → (P=Q f .to Pf) ,
      λ g Qg → min g (P=Q g .from Qg)
    ; from = λ (Qf , min) → (P=Q f .from Qf) ,
      λ g Qg → min g (P=Q g .to Qg)
    }
    where open Equivalence

  ext≗
    : {P Q : 𝐘 C}
    → (f : Mor C D)
    → P ≗ Q
    → P [ f ⨟] ≗ Q [ f ⨟]
  ext≗ {C} {D} f P=Q {E} g =
    record { to = P=Q (f ⨟ g) .to ; from = P=Q (f ⨟ g) .from }
    where open Equivalence

  ext∘ext≗
    : (P : 𝐘 C) (f : Mor C D) (g : Mor D E)
    → P [ f ⨟ g ⨟] ≗ P [ f ⨟] [ g ⨟]
  ext∘ext≗ P f g h = record
    { to   = subst (P _) (⨟-assoc f g _)
    ; from = subst (P _) (sym $ ⨟-assoc f g _)
    }
    
  P=Pid⨟-
    : (P : 𝐘 C)
    → P ≗ P [ id ⨟]
  P=Pid⨟- P {D} f = record
    { to   = subst (P D) (sym (⨟-idₗ f))
    ; from = subst (P D) (⨟-idₗ f)
    }

  Min-id
    : (P : 𝐘 C)
    → P C id
    → Min P _ id
  Min-id P Pid = Pid , λ g Pg → g , (⨟-idₗ g)

  Min-⨟-id
    : (P : 𝐘 C) (f : Mor C D)
    → Min P D f
    → Min P D (f ⨟ id)
  Min-⨟-id P f Pf = subst (Min P _) (sym (⨟-idᵣ _)) Pf
open IsCategory ⦃...⦄ public

record Category : Set₁ where
  field
    Obj        : Set
    Mor        : Obj → Obj → Set
    isCategory : IsCategory Obj Mor
open Category

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

  private variable
    A B C D E : Obj
  
  infix 6 _≈_
  
  _≈_
    : (x y : F C) → 𝐘 C
  (x ≈ y) _ f = x ⟨ f ⟩ ≡ y ⟨ f ⟩

  ≈-sym : (x y : F C) 
    → x ≈ y ≗ y ≈ x
  ≈-sym x y σ = record
    { to   = sym
    ; from = sym }
    where open Equivalence
    
  ≈-↑
    : (σ : Mor C D) (ρ : Mor D E) (γ : Mor E A)
    → (t u : F C)
    → (t ≈ u [ σ ⨟]) _ ρ
    → (t ≈ u [ σ ⨟]) _ (ρ ⨟ γ)
  ≈-↑ σ ρ γ t u eq = begin
    t ⟨ σ ⨟ (ρ ⨟ γ) ⟩
      ≡⟨ cong (t ⟨_⟩) (sym $ ⨟-assoc σ ρ γ) ⟩
    t ⟨ (σ ⨟ ρ) ⨟ γ ⟩
      ≡⟨ ⟨⟩-⨟ (σ ⨟ ρ) γ t ⟩
    t ⟨ σ ⨟ ρ ⟩ ⟨ γ ⟩
      ≡⟨ cong (_⟨ γ ⟩) eq ⟩
    u ⟨ σ ⨟ ρ ⟩ ⟨ γ ⟩
      ≡⟨ sym (⟨⟩-⨟ (σ ⨟ ρ) γ u) ⟩
    u ⟨ σ ⨟ ρ ⨟ γ ⟩
      ≡⟨ cong (u ⟨_⟩) (⨟-assoc σ ρ γ) ⟩
    u ⟨ σ ⨟ (ρ ⨟ γ) ⟩
      ∎

  t⟨fgh⟩=t⟨f⟩⟨gh⟩
    : (x : F A) (f : Mor A B) (g : Mor B C) (h : Mor C D)
    → x ⟨ f ⨟ g ⨟ h ⟩ ≡ x ⟨ f ⟩ ⟨ g ⨟ h ⟩
  t⟨fgh⟩=t⟨f⟩⟨gh⟩ x f g h = begin
    x ⟨ f ⨟ g ⨟ h ⟩
      ≡⟨ cong (x ⟨_⟩) (⨟-assoc f g h) ⟩
    x ⟨ f ⨟ (g ⨟ h) ⟩
      ≡⟨ ⟨⟩-⨟ f (g ⨟ h) x ⟩
    x ⟨ f ⟩ ⟨ g ⨟ h ⟩
      ∎

open IsPresheaf ⦃...⦄ public


-- {-
-- record Functor
--   {Obj₁ : Set} {Mor₁ : Obj₁ → Obj₁ → Set} ⦃ isCat₁ : IsCategory Obj₁ Mor₁ ⦄ 
--   {Obj₂ : Set} {Mor₂ : Obj₂ → Obj₂ → Set} ⦃ isCat₂ : IsCategory Obj₂ Mor₂ ⦄ 
--   (Fₒ : Obj₁ → Obj₂)  : Set where
--   field
--     Fₘ  : {A B : Obj₁}
--       → Mor₁ A B → Mor₂ (Fₒ A) (Fₒ B)
--     Fₘ-id : {A : Obj₁} → Fₘ {A} id ≡ id
--     Fₘ-⨟  : {A B C : Obj₁}
--       → (f : Mor₁ A B) (g : Mor₁ B C)
--       → Fₘ (f ⨟ g) ≡ Fₘ f ⨟ Fₘ g
-- open Functor ⦃...⦄ public
-- module _
--   {Obj₁ : Set} {Mor₁ : Obj₁ → Obj₁ → Set} ⦃ isCat₁ : IsCategory Obj₁ Mor₁ ⦄ 
--   {Obj₂ : Set} {Mor₂ : Obj₂ → Obj₂ → Set} ⦃ isCat₂ : IsCategory Obj₂ Mor₂ ⦄ 
--   {Fₒ : Obj₁ → Obj₂} ⦃ func : Functor Fₒ ⦄
--   (P : Obj₂ → Set)
--   ⦃ isPresheaf : IsPresheaf P ⦄ where

--   presheaf∘functor : IsPresheaf λ C → P (Fₒ C)
--   presheaf∘functor ._⟨_⟩  x f = x ⟨ Fₘ f ⟩
--   presheaf∘functor .⟨⟩-id {C} x = begin
--     x ⟨ Fₘ id ⟩
--       ≡⟨ cong (x ⟨_⟩) Fₘ-id ⟩
--     x ⟨ id ⟩
--       ≡⟨ ⟨⟩-id _ ⟩
--     x
--       ∎
--   presheaf∘functor .⟨⟩-⨟ f g x  = begin
--     x ⟨ Fₘ (f ⨟ g) ⟩
--       ≡⟨ cong (x ⟨_⟩) (Fₘ-⨟ f g) ⟩
--     x ⟨ Fₘ f ⨟ Fₘ g ⟩
--       ≡⟨ ⟨⟩-⨟ (Fₘ f) (Fₘ g) x ⟩
--     x ⟨ Fₘ f ⟩ ⟨ Fₘ g ⟩
--       ∎
-- -}
