open import Prelude

module Language.BiUntyped.Term where

open import Language.Type

infixr 5 ƛ_
infixl 7 _·_
infixr 8 ⟪_⟫_ ⟨_⟩_
infixr 9 `_ -- #_

pattern chk = false
pattern inf = true

data Λ (X : Type) : Bool → Type where
  `_
    : (x : X)
    → Λ X inf
  anno
    : (A : Ty)
    → Λ X chk 
    → Λ X inf
  conv
    : Λ X inf
    → Λ X chk
  _·_
    : Λ X inf → Λ X chk
    → Λ X inf
  ƛ_
    : Λ (X ⁺) chk
    → Λ X     chk

pattern _⦂_ t A = anno A t

private
  variable
    Γ Δ : Type
    m   : Bool

Ren : (Γ Δ : Type) → Type
Ren Γ Δ = Δ → Γ

ext : ∀ {Γ Δ}
  → Ren Γ Δ → Ren (Γ ⁺) (Δ ⁺)
ext ρ Z     = Z
ext ρ (S x) = S ρ x

⟨_⟩_ : ∀ {Γ Δ}
  → Ren Γ Δ → Λ Δ m → Λ Γ m
⟨ ρ ⟩ (` x)    = ` ρ x
⟨ ρ ⟩ anno A t = anno A (⟨ ρ ⟩ t)
⟨ ρ ⟩ conv t   = conv (⟨ ρ ⟩ t)
⟨ ρ ⟩ (t · u) = ⟨ ρ ⟩ t · ⟨ ρ ⟩ u
⟨ ρ ⟩ (ƛ t)   = ƛ ⟨ ext ρ ⟩ t

Sub : (Γ Δ : Type) → Type
Sub Γ Δ = Δ → Λ Γ inf

exts : ∀ {Γ Δ}
  → Sub Γ Δ → Sub (Γ ⁺) (Δ ⁺)
exts σ Z     = ` Z
exts σ (S x) = ⟨ S_ ⟩ σ x

⟪_⟫_
  : ∀ {Δ Γ}
  → (Δ   → Λ Γ inf)
  → (Λ Δ m → Λ Γ m)
⟪ σ ⟫ (` x)   = σ x
⟪ σ ⟫ (t · u) = ⟪ σ ⟫ t · ⟪ σ ⟫ u
⟪ σ ⟫ (ƛ t)   = ƛ ⟪ exts σ ⟫ t
⟪ σ ⟫ anno A t = anno A (⟪ σ ⟫ t)
⟪ σ ⟫ conv t   = conv (⟪ σ ⟫ t)

-- _∷_ : Sub Γ Δ → Λ Γ → Sub Γ (Δ ⁺)
-- (σ ∷ t) Z     = t
-- (σ ∷ t) (S x) = σ x

_⨟_
  : {Z : Type}
  → Sub Γ Δ → Sub Δ Z → Sub Γ Z
(σ ⨟ σ′) x = ⟪ σ ⟫ σ′ x

⇑_ : Ren Γ Δ → Sub Γ Δ
(⇑ ρ) x = ` ρ x

subst-idR : (σ : Sub Γ Δ)
  → (x : Δ)
  → ⟪ σ ⟫ (` x) ≡ σ x
subst-idR σ x = refl

exts-ids=ids
  : (x : (Γ ⁺))
  → exts `_ x ≡ ` x
exts-ids=ids Z     = refl
exts-ids=ids (S x) = refl

subst-idL : (t : Λ Γ m)
  → ⟪ `_ ⟫ t ≡ t
subst-idL (` x)   = refl
subst-idL (anno A t) = cong (anno A) (subst-idL t)
subst-idL (conv t)   = cong conv (subst-idL t)
subst-idL (t · u) = cong₂ _·_ (subst-idL t) (subst-idL u)
subst-idL (ƛ t)   = cong ƛ_ (
  ⟪ exts `_ ⟫ t
    ≡[ i ]⟨ ⟪ (λ x → exts-ids=ids x i) ⟫ t ⟩
  ⟪ `_ ⟫ t
    ≡⟨ subst-idL t ⟩
  t ∎)
  where open ≡-Reasoning

-- tedious to prove
postulate
  ren-exts : (σ : Sub Γ Δ)
    → (t : Λ Δ m)
    → ⟪ exts σ ⟫ ⟨ S_ ⟩ t ≡ ⟨ S_ ⟩ ⟪ σ ⟫ t

exts-comp : {Z : Type}
  → (σ : Sub Γ Δ) (σ′ : Sub Δ Z)
  → (x : (Z ⁺))
  → (exts σ ⨟ exts σ′) x ≡ exts (σ ⨟ σ′) x
exts-comp σ σ′ Z     = refl
exts-comp σ σ′ (S x) = begin
  (exts σ ⨟ exts σ′) (S x)
    ≡⟨ refl ⟩
  ⟪ exts σ ⟫ ⟨ S_ ⟩ (σ′ x)
    ≡⟨ ren-exts σ (σ′ x) ⟩
  ⟨ S_ ⟩ ⟪ σ ⟫ (σ′ x)
    ≡⟨ refl ⟩
  exts (σ ⨟ σ′) (S x) ∎
  where open ≡-Reasoning

subst-assoc
  : {Z : Type}
  → (σ : Sub Γ Δ) (σ′ : Sub Δ Z)
  → (t : Λ Z m)
  → ⟪ σ ⟫ ⟪ σ′ ⟫ t ≡ ⟪ σ ⨟ σ′ ⟫ t
subst-assoc σ σ′ (` x)   = refl
subst-assoc σ σ′ (anno A t) = cong (anno A) (subst-assoc σ σ′ t)
subst-assoc σ σ′ (conv t)   = cong conv (subst-assoc σ σ′ t)
subst-assoc σ σ′ (t · u) = cong₂ _·_
  (subst-assoc σ σ′ t) (subst-assoc σ σ′ u)
subst-assoc σ σ′ (ƛ t)   = cong ƛ_
  (⟪ exts σ ⟫ ⟪ exts σ′ ⟫ t
    ≡⟨ subst-assoc (exts σ) (exts σ′) t ⟩
  ⟪ exts σ ⨟ exts σ′ ⟫ t
    ≡[ i ]⟨ ⟪ (λ x → exts-comp σ σ′ x i) ⟫ t ⟩
   ⟪ exts (σ ⨟ σ′) ⟫ t ∎)
  where open ≡-Reasoning
