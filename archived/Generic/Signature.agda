open import Prelude

module Generic.Signature where

open import Language.Type
open import Category.Functor 

data RecD : Type where
  ι  : RecD
  δ_ : RecD → RecD

data ConD : Type₁ where
  ι : ConD
  σ : (A : Type) (D : A → ConD) → ConD
  ρ : (R : RecD) (D : ConD)     → ConD

data ConDs : Type₁ where
  []  : ConDs
  _∷_ : (D : ConD) (Ds : ConDs) → ConDs

syntax σ A (λ a → D) = σ[ a ∶ A ] D
syntax ρ R D         = ρ[     R ] D

infixr 5 _∷_

⟦_⟧ʳ : RecD → (T : Type → Type) (Γ : Type) → Type
⟦ ι   ⟧ʳ T Γ = T Γ
⟦ δ R ⟧ʳ T Γ = ⟦ R ⟧ʳ T (Γ ⁺)

⟦_⟧ᶜ : ConD → (T : Type → Type) (Γ : Type) → Type
⟦ ι ⟧ᶜ     T Γ = ⊤
⟦ σ A D ⟧ᶜ T Γ = Σ[ a ∈ A ] ⟦ D a ⟧ᶜ T Γ
⟦ ρ R D ⟧ᶜ T Γ = ⟦ R ⟧ʳ T Γ × ⟦ D ⟧ᶜ T Γ 

⟦_⟧ : ConDs → (T : Type → Type) (Γ : Type) → Type
⟦ []     ⟧ T Γ = ⊥
⟦ D ∷ [] ⟧ T Γ = ⟦ D ⟧ᶜ T Γ
⟦ D ∷ Ds ⟧ T Γ = ⟦ D ⟧ᶜ T Γ ⊎ ⟦ Ds ⟧ T Γ

private
  variable
    Γ Δ  : Type
    
module _ {T : Type → Type} ⦃ _ : RawFunctor T ⦄ where
  open RawFunctor ⦃...⦄

  mapʳ : (R : RecD)
    → (f : Γ → Δ)
    → ⟦ R ⟧ʳ T Γ → ⟦ R ⟧ʳ T Δ
  mapʳ ι     f x = fmap f x
  mapʳ (δ R) f x = mapʳ R (ext f) x

  mapᶜ : (D : ConD)
    → (f : Γ → Δ)
    → ⟦ D ⟧ᶜ T Γ → ⟦ D ⟧ᶜ T Δ
  mapᶜ ι       _ _       = tt
  mapᶜ (σ A D) f (a , x) = a , mapᶜ (D a) f x
  mapᶜ (ρ R D) f (x , y) = mapʳ R f x , mapᶜ D f y

  map : (Ds : ConDs)
    → (f : Γ → Δ)
    → ⟦ Ds ⟧ T Γ → ⟦ Ds ⟧ T Δ
  map (D ∷ [])         f x = mapᶜ D f x
  map (D ∷ Ds@(_ ∷ _)) f (inl x) = inl (mapᶜ D f x)
  map (D ∷ Ds@(_ ∷ _)) f (inr x) = inr (map Ds f x)

module _
  {T : Type → Type} ⦃ _ : RawFunctor T ⦄
  {Z : Type → Type} ⦃ _ : RawPtFunctor Z ⦄ where
  open RawPtFunctor ⦃...⦄

  strʳ : (R : RecD) → ⟦ R ⟧ʳ T (Z Γ) → ⟦ R ⟧ʳ (T ∘ Z) Γ 
  strʳ ι     x = x
  strʳ (δ R) x = strʳ R (mapʳ R f x)
    where
      f : Z Γ ⁺ → Z (Γ ⁺) 
      f z     = pure z
      f (s x) = fmap s_ x

  strᶜ : (D : ConD) → ⟦ D ⟧ᶜ T (Z Γ) → ⟦ D ⟧ᶜ (T ∘ Z) Γ
  strᶜ ι       _       = tt
  strᶜ (σ A D) (a , x) = a , strᶜ (D a) x
  strᶜ (ρ R D) (x , y) = strʳ R x , strᶜ D y

  str : (Ds : ConDs) → ⟦ Ds ⟧ T (Z Γ) → ⟦ Ds ⟧ (T ∘ Z) Γ
  str (D ∷ [])         x = strᶜ D x
  str (D ∷ Ds@(_ ∷ _)) (inl x) = inl (strᶜ D x)
  str (D ∷ Ds@(_ ∷ _)) (inr x) = inr (str Ds x)

record Signature (O : Type) : Type₁ where
  constructor sig
  field arity : O → List ℕ
open Signature

expandᶜ : ConD → Type
expandᶜ ι       = ⊤
expandᶜ (σ A D) = Σ[ a ∈ A ] expandᶜ (D a)
expandᶜ (ρ R D) = expandᶜ D

expand : ConDs → Type
expand []       = ⊥
expand (D ∷ []) = expandᶜ D
expand (D ∷ Ds) = expandᶜ D ⊎ expand Ds

toSigʳ : (R : RecD) → ℕ
toSigʳ ι     = 0
toSigʳ (δ R) = suc (toSigʳ R)

toSigᶜ : (D : ConD) → expandᶜ D → List ℕ
toSigᶜ ι       _       = []
toSigᶜ (σ A D) (a , o) = toSigᶜ (D a) o
toSigᶜ (ρ R D) t       = toSigʳ R ∷ toSigᶜ D t 

toSig′ : (Ds : ConDs) → expand Ds → List ℕ
toSig′ []               o = []
toSig′ (D ∷ [])         o = toSigᶜ D o
toSig′ (D ∷ Ds@(_ ∷ _)) (inl o) = toSigᶜ D o
toSig′ (D ∷ Ds@(_ ∷ _)) (inr o) = toSig′ Ds o

toSig : (Ds : ConDs) → Signature (expand Ds)
arity (toSig Ds) = toSig′ Ds

LC : ConDs
LC = ρ[ ι ] ρ[ ι ] ι ∷ ρ[ δ ι ] ι ∷ []

data Λₒ : Type where
  app lam : Λₒ

Λ∶Sig : Signature Λₒ
Λ∶Sig = sig λ where
  app → 0 ∷ 0 ∷ []
  lam → 1 ∷ []
