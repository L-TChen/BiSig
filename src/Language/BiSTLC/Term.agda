open import Prelude

module Language.BiSTLC.Term where

open import Language.Type

infixr 5 ƛ_
infixl 7 _·_
infixr 8 ⟪_⟫_ ⟨_⟩_
infixr 9 `_ -- #_
 
pattern chk = false
pattern inf = true

private
  variable
    A B C          : Ty
    Γ Δ Ξ          : Ty → Type
    m              : Bool

data Tm (Γ : Ty → Type) : Bool → Ty → Type where
  `_
    : (x : Γ A)
    → Tm Γ inf A
  anno
    : (A : Ty)
    → Tm Γ chk A
    → Tm Γ inf A
  conv
    : A ≡ B
    → Tm Γ inf A
    → Tm Γ chk B
  _·_
    : Tm Γ inf (A ⇒ B) → (Tm Γ chk A)
    → Tm Γ inf B
  ƛ_
    : Tm (Γ ▷ A) chk B
    → Tm Γ chk (A ⇒ B)

infix 10 _⦂_
pattern _⦂_ t A = anno A t

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
⟨_⟩_ : Ren Γ Δ → Tm Δ m A → Tm Γ m A
⟨ ρ ⟩ ` x     = ` ρ x
⟨ ρ ⟩ (t ⦂ A) = (⟨ ρ ⟩ t) ⦂ A
⟨ ρ ⟩ (conv p t) = conv p (⟨ ρ ⟩ t)
⟨ ρ ⟩ (t · u) = ⟨ ρ ⟩ t · ⟨ ρ ⟩ u
⟨ ρ ⟩ (ƛ t)   = ƛ ⟨ ext ρ ⟩ t

postulate
-- map id = id
  ren-id
    : (t : Tm Γ m A)
    → ⟨ id ⟩ t ≡ t
-- map (f ∘ g) = map f ∘ map g
  ren-comp
    : (ρ : Ren Γ Δ) (ρ′ : Ren Δ Ξ)
    → (t : Tm Ξ m A)
    → ⟨ ρ ∘ ρ′ ⟩ t ≡ ⟨ ρ ⟩ ⟨ ρ′ ⟩ t

Sub : (Γ Δ : Ty → Type) → Type
Sub Γ Δ = {A : Ty} → Δ A → Tm Γ inf A

exts : Sub Γ Δ → Sub (Γ ▷ A) (Δ ▷ A)
exts σ Z     = ` Z
exts σ (S x) = ⟨ S_ ⟩ σ x

⟪_⟫_ : Sub Γ Δ → (Tm Δ m A → Tm Γ m A)
⟪ σ ⟫ ` x     = σ x
⟪ σ ⟫ t ⦂ _   = (⟪ σ ⟫ t) ⦂ _
⟪ σ ⟫ (conv p t) = conv p (⟪ σ ⟫ t)
⟪ σ ⟫ (t · u) = ⟪ σ ⟫ t · ⟪ σ ⟫ u
⟪ σ ⟫ (ƛ t)   = ƛ ⟪ exts σ ⟫ t

_∷_ : Sub Γ Δ → Tm Γ inf A → Sub Γ (Δ ▷ A)
(σ ∷ t) Z     = t
(σ ∷ t) (S x) = σ x

[_]_
  : Tm Γ       inf B
  → Tm (Γ ▷ B) m   A 
  → Tm Γ       m   A
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

subst-idL : (t : Tm Γ m A)
  → ⟪ `_ ⟫ t ≡ t
subst-idL (` x)   = refl
subst-idL (conv p t) = cong (conv p) (subst-idL t) 
subst-idL (t ⦂ A) = cong (anno A) (subst-idL t)
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
    → (t : Tm Δ m A)
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
  → (t : Tm Z m A)
  → ⟪ σ ⟫ ⟪ σ′ ⟫ t ≡ ⟪ σ ⨟ σ′ ⟫ t
subst-assoc σ σ′ (` x)   = refl
subst-assoc σ σ′ (t ⦂ A) = cong (anno A) (subst-assoc σ σ′ t)
subst-assoc σ σ′ (conv p t) = cong (conv p) (subst-assoc σ σ′ t)
subst-assoc σ σ′ (t · u) = cong₂ _·_
  (subst-assoc σ σ′ t) (subst-assoc σ σ′ u)
subst-assoc σ σ′ (ƛ t)   = cong ƛ_
  (⟪ exts σ ⟫ ⟪ exts σ′ ⟫ t
    ≡⟨ subst-assoc (exts σ) (exts σ′) t ⟩
  ⟪ exts σ ⨟ exts σ′ ⟫ t
    ≡[ i ]⟨ ⟪ (λ x → exts-comp σ σ′ x i) ⟫ t ⟩
   ⟪ exts (σ ⨟ σ′) ⟫ t ∎)
  where open ≡-Reasoning
