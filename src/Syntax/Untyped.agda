open import Prelude

module Syntax.Untyped where

private
  variable
    n m : ℕ
    O : Set

record Signature (O : Set) : Set where
  constructor sig
  field
    ∣_∣ : O → List ℕ

  Arity = ∣_∣
open Signature

⟦_⟧ᵇ : ℕ → (ℕ → Set ℓ) → ℕ → Set ℓ
⟦ zero  ⟧ᵇ  T n = T n
⟦ suc a ⟧ᵇ T n = ⟦ a ⟧ᵇ T (suc n)

⟦_⟧ᶜ : (as : List ℕ) (T : ℕ → Set ℓ) → (ℕ → Set ℓ)
⟦ []     ⟧ᶜ _ _ = ⊤
⟦ a ∷ as ⟧ᶜ T n = ⟦ a ⟧ᵇ T n × ⟦ as ⟧ᶜ T n

infixr -10 _-→_
_-→_ : (T : ℕ → Set ℓ₁) (T : ℕ → Set ℓ₂) → Set _
(T -→ U) = ∀ {n} → T n → U n

⟦_⟧ : (s : Signature O) (T : ℕ → Set ℓ) → ℕ → Set ℓ
⟦_⟧ {O} (sig ar) T n = Σ[ o ∈ O ] ⟦ ar o ⟧ᶜ T n

record _-Alg (s : Signature O) (T : ℕ → Set ℓ) : Set ℓ where
  constructor _,_
  field
    var : Fin     -→ T
    alg : ⟦ s ⟧ T -→ T

module Term {O : Set} (s : Signature O) where

  infix 40 `_
  
  data Tm (n : ℕ) : Set where
    `_ : Fin n        → Tm n
    op : (⟦ s ⟧ Tm) n → Tm n

  module _ {T : ℕ → Set ℓ} (α : (s -Alg) T) where
    open _-Alg α

    fold : Tm -→ T
    foldMap : (s : Signature O) → ⟦ s ⟧ Tm -→ ⟦ s ⟧ T
    foldMapᶜ : (as : List ℕ) → ⟦ as ⟧ᶜ Tm -→ ⟦ as ⟧ᶜ T
    foldMapᵇ : ∀ a {n} → ⟦ a ⟧ᵇ Tm n → ⟦ a ⟧ᵇ T n

    fold (` x)  = var x
    fold (op x) = alg (foldMap s x)
    foldMap (sig ar) (o , as) = o , foldMapᶜ (ar o) as
    foldMapᶜ []       _       = _
    foldMapᶜ (a ∷ as) (t , u) = foldMapᵇ a t , foldMapᶜ as u
    foldMapᵇ zero    t = fold t
    foldMapᵇ (suc a) t = foldMapᵇ a t

  heightAlg : (s -Alg) λ n → (Fin n → ℕ) → ℕ
  heightAlg = (λ x ρ → ρ x) , λ where (o , ts) ρ → suc $ f (Arity s o) ts ρ
    where 
      g : ∀ a → ⟦ a ⟧ᵇ (λ n → ((Fin n) → ℕ) → ℕ) n → ((Fin n) → ℕ) → ℕ 
      g zero    t = t
      g (suc a) t ρ = g a t λ where zero → 0 ; (suc x) → ρ x

      f : ∀ as → ⟦ as ⟧ᶜ (λ n → ((Fin n) → ℕ) → ℕ) n → ((Fin n) → ℕ) → ℕ 
      f []       _       _ = 0
      f (a ∷ as) (t , u) ρ = g a t ρ ⊔ f as u ρ
{-
  height : Tm n → (Fin n → ℕ) → ℕ
  heightMap  : ∀ {s}         → ⟦ s ⟧   Tm n → (Fin n → ℕ) → ℕ
  heightMapᶜ : (as : List ℕ) → ⟦ as ⟧ᶜ Tm n → (Fin n → ℕ) → ℕ
  heightMapᵇ : (a : ℕ)       → ⟦ a ⟧ᵇ  Tm n → (Fin n → ℕ) → ℕ

  height (` x)  ρ = ρ x
  height (op x) ρ = 1 + heightMap x ρ
  heightMap {s = sig ar} (o , t) ρ = heightMapᶜ (ar o) t ρ
  heightMapᶜ []       _       _ = 0
  heightMapᶜ (a ∷ as) (t , u) ρ = heightMapᵇ a t ρ  ⊔ heightMapᶜ as u ρ
  heightMapᵇ zero    t ρ = height t ρ
  heightMapᵇ (suc a) t ρ = heightMapᵇ a t λ where
    zero    → 0
    (suc x) → ρ x
-}

  height : Tm n → ℕ
  height t = fold heightAlg t (λ _ → 0)
      
data Λₒ : Set where
  app abs : Λₒ

Λ∶Sig : Signature Λₒ
∣ Λ∶Sig ∣ = λ where
  app → 0 ∷ 0 ∷ []
  abs → 1 ∷ []

open Term Λ∶Sig

pattern ƛ_ t    = op (abs , t , _)
pattern _·_ t u = op (app , t , u , _)

identity : Tm 0
identity = ƛ ` (# 0)

projection : Tm 0
projection = ƛ ƛ (` (# 0) · ` (# 1))

s : ℕ
s = height identity
