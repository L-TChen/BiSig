{-# OPTIONS --safe #-}

module Prelude.Category where

open import Relation.Binary.PropositionalEquality
  hiding (_≗_; isEquivalence)
open import Relation.Nullary.Decidable
open import Relation.Binary
  hiding (_⇒_; _⇔_; Min)

open import Data.Product
open import Data.Empty
  using (⊥)
open import Level
open import Function using (_$_; _∘_)
open import Relation.Nullary.Reflects     

open import Prelude.Equivalence
open import Prelude.Logic

open ≡-Reasoning


private variable
  a b c : Level

record IsCategory (Obj : Set) (Mor : Obj → Obj → Set) (_≈_ : ∀ {X Y} → Rel (Mor X Y) 0ℓ) : Set where
  infixl 5 _⨟_
  field
    isEquivalence : ∀ {X Y} → IsEquivalence (_≈_ {X} {Y})

    id      : {C     : Obj} → Mor C C
    _⨟_     : {C D E : Obj} → Mor C D → Mor D E → Mor C E
    
    ⨟-idᵣ   : {C D   : Obj}
      → (f : Mor C D)
      → (f ⨟ id) ≈ f

    ⨟-idₗ   : {C D   : Obj}
      → (f : Mor C D)
      → (id ⨟ f) ≈ f

    ⨟-assoc : {C D E F : Obj}
      → (f : Mor C D) (g : Mor D E) (h : Mor E F)
      → ((f ⨟ g) ⨟ h) ≈ (f ⨟ (g ⨟ h))

  𝐘 : Obj → Set₁
  𝐘 C = (D : Obj) → Mor C D → Set

  private variable
    B C D E : Obj
    P Q     : 𝐘 C

  infixl 5 _∧_
  infix 4 _⊒_ _⊑_
  infix  3 ¬′_
--  infix  2 _≗_
  
  _⊒_ _⊑_
    : {C D E : Obj}
    → Mor C D → Mor C E → Set
  _⊒_ {C} {D} {E} f g = Σ[ h ∈ Mor E D ] (g ⨟ h) ≈ f

  _⊑_ f g = g ⊒ f


  _∧_ : (P Q : 𝐘 C) → 𝐘 C
  (P ∧ Q) D f = P D f × Q D f

  ⊥′ : 𝐘 C
  ⊥′ _ _ = ⊥

  ¬′_ : (X : 𝐘 C) → Set _
  ¬′_  X = X ⇒ ⊥′
  
--  _≗_ : (X Y : 𝐘 C) → Set _
--  X ≗ Y = ∀ {i} j → X i j ⇔ Y i j
--
--  ≗→⇔ : P ≗ Q → ∃₂ P ⇔ ∃₂ Q
--  ≗→⇔ P=Q = record
--    { to   = map₂ (map₂ (P=Q _ .to))
--    ; from = map₂ (map₂ (P=Q _ .from))
--    }
--    where open Equivalence

  _[_⨟]
    : (P : 𝐘 C) (f : Mor C D) 
    → 𝐘 D
  (P [ f ⨟]) _ g = P _ (f ⨟ g)

  infixl 5 _[_⨟]
  
  Min : 𝐘 C → 𝐘 C
  Min {C} P D f = P D f ×
    (∀ {D} (g : Mor C D) → P D g → f ⊑ g)

  ↑-closed : 𝐘 C → Set
  ↑-closed {C} P = ∀ {D E} (f : Mor C D) (g : Mor C E)
    → f ⊑ g → P _ f → P _ g  

--  Min≗
--    : P ≗ Q
--    → Min P ≗ Min Q
--  Min≗ P=Q f = record
--    { to   = λ (Pf , min) → (P=Q f .to Pf) ,
--      λ g Qg → min g (P=Q g .from Qg)
--    ; from = λ (Qf , min) → (P=Q f .from Qf) ,
--      λ g Qg → min g (P=Q g .to Qg)
--    }
--    where open Equivalence

--  ext≗
--    : (f : Mor C D)
--    → P ≗ Q
--    → P [ f ⨟] ≗ Q [ f ⨟]
--  ext≗ {C} {D} f P=Q {E} g =
--    record { to = P=Q (f ⨟ g) .to ; from = P=Q (f ⨟ g) .from }
--    where open Equivalence

--  ext∘ext≗
--    : (P : 𝐘 C) (f : Mor C D) (g : Mor D E)
--    → P [ f ⨟ g ⨟] ≗ P [ f ⨟] [ g ⨟]
--  ext∘ext≗ P f g h = record
--    { to   = {!!} -- subst (P _) (⨟-assoc f g _)
--    ; from = {!!} -- subst (P _) (sym $ ⨟-assoc f g _)
--    }
--    
--  P=Pid⨟-
--    : (P : 𝐘 C)
--    → P ≗ P [ id ⨟]
--  P=Pid⨟- P {D} f = record
--    { to   = {!!} -- subst (P D) (sym (⨟-idₗ f))
--    ; from = {!!} -- subst (P D) (⨟-idₗ f)
--    }

  Min-id
    : (P : 𝐘 C)
    → P C id
    → Min P _ id
  Min-id P Pid = Pid , λ g Pg → g , (⨟-idₗ g)
--
--  Min-⨟-id
--    : (P : 𝐘 C) (f : Mor C D)
--    → Min P D f
--    → Min P D (f ⨟ id)
--  Min-⨟-id P f Pf = {!!} , {!!} -- subst (Min P _) (sym (⨟-idᵣ _)) Pf

--  failure-propagate
--    : (f : Mor C D) (g : Mor D E)
--    → Min (P [ f ⨟]) _ g
--    → ¬′ Q [ f ⨟ g ⨟]
--    → ¬′ P ∧ Q [ f ⨟]
--  failure-propagate {Q = Q} f g Pρ ¬Q {_} {h} P∧Q =
--    let (i , f⨟i=h) = Pρ .proj₂ h (P∧Q .proj₁) in
--    ¬Q (subst (Q _) (begin
--      f ⨟ h
--        ≡⟨ {!!} ⟩ -- cong (f ⨟_) (sym $ f⨟i=h) ⟩
--      f ⨟ (g ⨟ i)
--        ≡⟨ {!!} ⟩ -- (sym $ ⨟-assoc f g i) ⟩
--      (f ⨟ g) ⨟ i ∎)
--    (P∧Q .proj₂))

--  optimist
--    : (P : 𝐘 C) (Q : 𝐘 C)
--    → (f : Mor C D) (g : Mor D E) (h : Mor E B)
--    → ↑-closed P → Min (P [ f ⨟]) _ g → Min (Q [ f ⨟ g ⨟]) _ h
--    → Min ((P ∧ Q) [ f ⨟]) _ (g ⨟ h)
--  optimist P Q f g h ↑P (Pfg , fMin) (Qfgh , fgMin) =
--    (↑P _ _ (h , ⨟-assoc _ _ _) Pfg , subst (Q _) (⨟-assoc _ _ _) Qfgh) , λ
--      i (Pfi , Qfi) →
--        let (j , g⨟j=i) = fMin i Pfi
--            (k , h⨟k=j) = fgMin j (subst (Q _) (f ⨟ i ≡⟨ cong (f ⨟_) (sym g⨟j=i) ⟩ f ⨟ (g ⨟ j) ≡⟨ (sym $ ⨟-assoc _ _ _) ⟩ (f ⨟ g) ⨟ j ∎) Qfi)
--        in k , (begin
--          (g ⨟ h) ⨟ k
--            ≡⟨ ⨟-assoc g h k ⟩
--          g ⨟ (h ⨟ k)
--            ≡⟨ cong (g ⨟_) h⨟k=j ⟩
--          g ⨟ j
--            ≡⟨ g⨟j=i ⟩
--          i
--           ∎)
    
open IsCategory ⦃...⦄ public

record Category : Set₁ where
  field
    Obj        : Set
    Mor        : Obj → Obj → Set
    _≈_        : {X Y : Obj} → Rel (Mor X Y) 0ℓ
    isCategory : IsCategory Obj Mor _≈_
open Category

record IsPresheaf {Obj : Set} {Mor : Obj → Obj → Set} {_≈_ : {X Y : Obj} → Rel (Mor X Y) 0ℓ}
  ⦃ isCat : IsCategory Obj Mor _≈_ ⦄ (F : Obj → Set) : Set where
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
  
--  infix 6 _≈_
--  _≈_
--    : (x y : F C) → 𝐘 C
--  (x ≈ y) _ f = x ⟨ f ⟩ ≡ y ⟨ f ⟩
--
--  ≈-sym : (x y : F C) 
--    → x ≈ y ≗ y ≈ x
--  ≈-sym x y σ = record
--    { to   = sym
--    ; from = sym }
--    where open Equivalence
--    
--  ≈-↑
--    : (t u : F C)
--    → ↑-closed (t ≈ u)
--  ≈-↑ t u σ ρ (γ , σ⨟γ=ρ) eq = begin
--    t ⟨ ρ ⟩
--      ≡⟨ cong (t ⟨_⟩) (sym σ⨟γ=ρ) ⟩
--    t ⟨ σ ⨟ γ ⟩
--      ≡⟨ ⟨⟩-⨟ σ γ t ⟩
--    t ⟨ σ ⟩ ⟨ γ ⟩
--      ≡⟨ cong (_⟨ γ ⟩) eq ⟩
--    u ⟨ σ ⟩ ⟨ γ ⟩
--      ≡⟨ sym (⟨⟩-⨟ σ γ u) ⟩
--    u ⟨ σ ⨟ γ ⟩
--      ≡⟨ cong (u ⟨_⟩) σ⨟γ=ρ ⟩
--    u ⟨ ρ ⟩
--      ∎
--
--  t⟨fgh⟩=t⟨f⟩⟨gh⟩
--    : (x : F A) (f : Mor A B) (g : Mor B C) (h : Mor C D)
--    → x ⟨ f ⨟ g ⨟ h ⟩ ≡ x ⟨ f ⟩ ⟨ g ⨟ h ⟩
--  t⟨fgh⟩=t⟨f⟩⟨gh⟩ x f g h = begin
--    x ⟨ f ⨟ g ⨟ h ⟩
--      ≡⟨ cong (x ⟨_⟩) (⨟-assoc f g h) ⟩
--    x ⟨ f ⨟ (g ⨟ h) ⟩
--      ≡⟨ ⟨⟩-⨟ f (g ⨟ h) x ⟩
--    x ⟨ f ⟩ ⟨ g ⨟ h ⟩
--      ∎

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
