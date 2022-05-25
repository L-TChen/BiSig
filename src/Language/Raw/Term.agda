{- From (Binding) Signatures to Substitution -}

open import Prelude

module Language.Raw.Term where

infixr 5 ƛ_
infixl 7 _·_
infixr 8 ⟪_⟫_ ⟨_⟩_
infixr 9 `_ -- #_

private
  variable
    Γ Δ Ξ          : Type

data Tm (Γ : Type) : Type where
  `_
    : Γ
    → Tm Γ
  _·_ -- binary operation
    : Tm Γ → Tm Γ
    → Tm Γ
  ƛ_ -- unary operation
    : Tm Γ
    → Tm Γ

Ren : (Γ Δ : Type) → Type
Ren Γ Δ = Δ → Γ

⟨_⟩_ : Ren Γ Δ → Tm Δ → Tm Γ
⟨ ρ ⟩ (` x)   = ` ρ x
⟨ ρ ⟩ (t · u) = ⟨ ρ ⟩ t · ⟨ ρ ⟩ u
⟨ ρ ⟩ (ƛ t)   = ƛ ⟨ ρ ⟩ t

Sub : (Γ Δ : Type) → Type
Sub Γ Δ = Δ → Tm Γ

-- bind : Tm Δ → (Δ → Tm Γ) → Tm Γ
⟪_⟫_
  : (Δ    → Tm Γ)
  → (Tm Δ → Tm Γ)
⟪ σ ⟫ (` x)   = σ x
⟪ σ ⟫ (t · u) = ⟪ σ ⟫ t · ⟪ σ ⟫ u
⟪ σ ⟫ (ƛ t)   = ƛ ⟪ σ ⟫ t

-- (Tm : Set → Set, `_ : X → Tm X, ⟪_⟫_) is a monad (the free monad over what?)
subst-idR : (σ : Sub Γ Δ)
  → (x : Δ)
  → ⟪ σ ⟫ (` x) ≡ σ x
subst-idR σ x = refl

-- `_ : Γ → Tm Γ
-- ⟪ `_ ⟫_ : Tm Γ → Tm Γ
subst-idL : (t : Tm Γ)
  → ⟪ `_ ⟫ t ≡ t
subst-idL (` x)   = refl
subst-idL (t · u) = cong₂ _·_ (subst-idL t) (subst-idL u)
subst-idL (ƛ t)   = cong ƛ_ (subst-idL t)
  
_⨟_
  : {Z : Type}
  → Sub Γ Δ → Sub Δ Z → Sub Γ Z
(σ ⨟ σ′) x = ⟪ σ ⟫ σ′ x

subst-assoc
  : (σ : Sub Γ Δ) (σ′ : Sub Δ Ξ)
  → (t : Tm Ξ)
  → ⟪ σ ⟫ ⟪ σ′ ⟫ t ≡ ⟪ σ ⨟ σ′ ⟫ t
subst-assoc σ σ′ (` x)   = refl
subst-assoc σ σ′ (t · u) = cong₂ _·_
  (subst-assoc σ σ′ t) (subst-assoc σ σ′ u)
subst-assoc σ σ′ (ƛ t)   = cong ƛ_ (subst-assoc σ σ′ t)

open import Cubical.Data.List
  using (List; []; _∷_)

data Mono : Type₁ where
  K     : (A : Type)   → Mono
  I     :                Mono -- U for Unit, I for Identity
  _⊗_   : (F G : Mono) → Mono

⟦_⟧ᵐ : Mono
  → (Type → Type)
⟦ K A   ⟧ᵐ _ = A
⟦ I     ⟧ᵐ X = X
⟦ F ⊗ G ⟧ᵐ X = ⟦ F ⟧ᵐ X × ⟦ G ⟧ᵐ X

Poly : Type₁
Poly = List Mono

private
  variable
    G H : Poly
    A B : Type

mapᵐ : (M : Mono) → (A → B)
  → ⟦ M ⟧ᵐ A → ⟦ M ⟧ᵐ B
mapᵐ (K _)   _ x = x
mapᵐ I       f x = f x
mapᵐ (M ⊗ N) f (x , y) = mapᵐ M f x , mapᵐ N f y

⟦_⟧ : Poly → Type → Type
⟦ []     ⟧ X = ⊥
⟦ F ∷ Fs ⟧ X = ⟦ F ⟧ᵐ X ⊎ ⟦ Fs ⟧ X

mapᵖ : (H : Poly) → (A → B)
  → ⟦ H ⟧ A → ⟦ H ⟧ B
mapᵖ(H ∷ Hs) f (inl x) = inl (mapᵐ  H f x)
mapᵖ(H ∷ Hs) f (inr x) = inr (mapᵖ Hs f x)

-- Mono --> constructor
-- Poly --> a list of constructors
-- μ_   --> data declaration

data μ_ (F : Poly) : Type where
  inn : ⟦ F ⟧ (μ F) → μ F

Alg : (F : Poly) → Type → Type
Alg F X = ⟦ F ⟧ X → X

fold : (F : Poly) {X : Type}
   → Alg F X → μ F → X
fold F α (inn x) = α (mapᵖ F {!(fold F α)!} x) 
{-
module _ (alg : ⟦ K A ∷ H ⟧ B → B) where
  mutual
    fold : FreeM H A → B
    fold (var a) = alg (inl a)
    fold (op xs) = alg (inr (mapFold _ xs))

    mapFold : ∀ G → ⟦ G ⟧ (μ (K A ∷ H)) → ⟦ G ⟧ B
    mapFold (G ∷ Gs) (inl xs) = inl (mapFoldᵐ G xs)
    mapFold (G ∷ Gs) (inr xs) = inr (mapFold Gs xs)

    mapFoldᵐ : ∀ G → ⟦ G ⟧ᵐ (μ (K A ∷ H)) → ⟦ G ⟧ᵐ B
    mapFoldᵐ (K A)    a          = a
    mapFoldᵐ I        x          = fold x
    mapFoldᵐ (G ⊗ G') (xs , xs') = mapFoldᵐ G xs , mapFoldᵐ G' xs'
-}

-- H : Signature
-- (A + H) (FreeM H A) ≅ FreeM H A
FreeM : (H : Poly) → Type → Type
FreeM H A = μ (K A ∷ H)

pattern var x = inn (inl x)
pattern op  t = inn (inr t)

_ : A                 → FreeM H A
_ = var
_ : ⟦ H ⟧ (FreeM H A) → FreeM H A
-- (⟦ Hᵢ ⟧ (FreeM H A) → FreeM H A)_i
_ = op

-- ⟪_⟫_
_=<<_
  : (A         → FreeM H B)
  → (FreeM H A → FreeM H B)
f =<< t = fold _ [ f , op ] t

TmF : Poly
TmF = (I ⊗ I) ∷ I ∷ []

Tm′ : Type → Type
Tm′ = FreeM TmF

pattern _·′_ t u = op (inl (t , u))
pattern ƛ′_ t    = op (inr (inl t))

toTm : Tm′ A → Tm A
toTm (var x)            = ` x
toTm (op (inl (x , y))) = toTm x · toTm y
toTm (op (inr (inl x))) = ƛ toTm x

fromTm : Tm A → Tm′ A
fromTm (` x)   = var x
fromTm (t · u) = fromTm t ·′ fromTm u
fromTm (ƛ t)   = ƛ′ fromTm t
