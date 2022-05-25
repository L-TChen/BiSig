open import Prelude

module Language.STLC.Term where

open import Language.Type

infixr 5 ƛ_
infixl 7 _·_
infixr 8 ⟪_⟫_ ⟨_⟩_
infixr 9 `_ -- #_

data Tm (Γ : Ty → Type) : Ty → Type

private
  variable
    A B C          : Ty
    Γ Δ Ξ          : Ty → Type
    t u v t′ u′ v′ : Tm Γ A

data Tm Γ where
  `_
    : (x : Γ A)
    → Tm Γ A
  _·_
    : (t : Tm Γ (A ⇒ B)) (u : Tm Γ A)
    → Tm Γ B
  ƛ_
    : Tm (Γ ▷ A) B
    → Tm Γ (A ⇒ B)

Ren : (Γ Δ : Ty → Type) → Type
Ren Γ Δ = ∀ {A} → Δ A → Γ A

_⨟ʳ_ : Ren Γ Δ → Ren Δ Ξ → Ren Γ Ξ
ρ ⨟ʳ ρ′ = ρ ∘ ρ′ 

ext : Ren Γ Δ → Ren (Γ ▷ A) (Δ ▷ A)
ext ρ Z     = Z
ext ρ (S x) = S ρ x

-- renaming is map:
-- (ρ : ∀ {A} → Δ A → Γ A)
-- -----------------------
-- ∀ {A} → Tm Δ A → Tm Γ A
⟨_⟩_ : Ren Γ Δ → Tm Δ A → Tm Γ A
⟨ ρ ⟩ (` x)   = ` ρ x
⟨ ρ ⟩ (t · u) = ⟨ ρ ⟩ t · ⟨ ρ ⟩ u
⟨ ρ ⟩ (ƛ t)   = ƛ ⟨ ext ρ ⟩ t

postulate
-- map id = id
  ren-id
    : (t : Tm Γ A)
    → ⟨ (λ x → x) ⟩ t ≡ t
-- map (f ∘ g) = map f ∘ map g
  ren-comp
    : (ρ : Ren Γ Δ) (ρ′ : Ren Δ Ξ)
    → (t : Tm Ξ A)
    → ⟨ ρ ∘ ρ′ ⟩ t ≡ ⟨ ρ ⟩ ⟨ ρ′ ⟩ t

Sub : (Γ Δ : Ty → Type) → Type
Sub Γ Δ = {A : Ty} → Δ A → Tm Γ A

exts : Sub Γ Δ → Sub (Γ ▷ A) (Δ ▷ A)
exts σ Z     = ` Z
exts σ (S x) = ⟨ S_ ⟩ σ x

⟪_⟫_ : Sub Γ Δ → (Tm Δ A → Tm Γ A)
⟪ σ ⟫ (` x)   = σ x
⟪ σ ⟫ (t · u) = ⟪ σ ⟫ t · ⟪ σ ⟫ u
⟪ σ ⟫ (ƛ t)   = ƛ ⟪ exts σ ⟫ t

_∷_ : Sub Γ Δ → Tm Γ A → Sub Γ (Δ ▷ A)
(σ ∷ t) Z     = t
(σ ∷ t) (S x) = σ x

[_]_
  : Tm Γ B
  → Tm (Γ ▷ B) A 
  → Tm Γ A
[ u ] t = ⟪ `_ ∷ u ⟫ t

_⨟_
  : {Z : Ty → Type}
  → Sub Γ Δ → Sub Δ Z → Sub Γ Z
(σ ⨟ σ′) x = ⟪ σ ⟫ σ′ x

⇑_ : Ren Γ Δ → Sub Γ Δ
(⇑ ρ) x = ` ρ x

subst-idR : (σ : Sub Γ Δ)
  → (x : Δ A)
  → ⟪ σ ⟫ (` x) ≡ σ x
subst-idR σ x = refl

exts-ids=ids
  : (x : (Γ ▷ B) A)
  → exts `_ x ≡ ` x
exts-ids=ids Z     = refl
exts-ids=ids (S x) = refl

subst-idL : (t : Tm Γ A)
  → ⟪ `_ ⟫ t ≡ t
subst-idL (` x)   = refl
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
    → (t : Tm Δ A)
    → ⟪ exts {A = B} σ ⟫ ⟨ S_ ⟩ t ≡ ⟨ S_ ⟩ ⟪ σ ⟫ t

exts-comp : {Z : Ty → Type}
  → (σ : Sub Γ Δ) (σ′ : Sub Δ Z)
  → (x : (Z ▷ B) A)
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
  : {Z : Ty → Type}
  → (σ : Sub Γ Δ) (σ′ : Sub Δ Z)
  → (t : Tm Z A)
  → ⟪ σ ⟫ ⟪ σ′ ⟫ t ≡ ⟪ σ ⨟ σ′ ⟫ t
subst-assoc σ σ′ (` x)   = refl
subst-assoc σ σ′ (t · u) = cong₂ _·_
  (subst-assoc σ σ′ t) (subst-assoc σ σ′ u)
subst-assoc σ σ′ (ƛ t)   = cong ƛ_
  (⟪ exts σ ⟫ ⟪ exts σ′ ⟫ t
    ≡⟨ subst-assoc (exts σ) (exts σ′) t ⟩
  ⟪ exts σ ⨟ exts σ′ ⟫ t
    ≡[ i ]⟨ ⟪ (λ x → exts-comp σ σ′ x i) ⟫ t ⟩
   ⟪ exts (σ ⨟ σ′) ⟫ t ∎)
  where open ≡-Reasoning

infix 3 _-→_
data _-→_ {Γ} : (t u : Tm Γ A) → 𝓤₀ ̇ where
  β-ƛ·
    : (ƛ t) · u -→ [ u ] t
  ξ-ƛ
    :   t -→ t′
    → ƛ t -→ ƛ t′    
  ξ-·ₗ
    :     t -→ t′
      ---------------
    → t · u -→ t′ · u
  ξ-·ᵣ
    :     u -→ u′
      ---------------
    → t · u -→ t · u′

data _-↠_ {Γ A} : (t u : Tm Γ A) → 𝓤₀ ̇ where
  _∎ : (t : Tm Γ A)
    → t -↠ t
    
  _-→⟨_⟩_
    : ∀ t   
    → t -→ u
    → u -↠ v
      -------
    → t -↠ v

infix  2 _-↠_ 
infixr 2 _-→⟨_⟩_
infix 3 _∎

_-↠⟨_⟩_
  : (t : Tm Γ A)
  → t -↠ u → u -↠ v
  -----------------
  → t -↠ v
t -↠⟨ t ∎         ⟩ w = w
t -↠⟨ t -→⟨ x ⟩ r ⟩ w = t -→⟨ x ⟩ _ -↠⟨ r ⟩ w

infixr 2 _-↠⟨_⟩_
