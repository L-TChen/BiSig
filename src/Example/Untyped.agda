open import Prelude

module Example.Untyped where

open import Generic.Signature
open import Generic.Algebra

open import Language.Type
open import Language.Untyped.Term

LC : ConDs
LC = ρ[ ι ] ρ[ ι ] ι
   ∷ ρ[ δ ι ] ι
   ∷ []

open import Generic.Term LC

pattern _·′_ t u = op₁ (t , u , tt)
pattern ƛ′_  t   = op₂ (t , tt)

private
  variable
    Γ Δ : Type

toΛ : Term Γ → Λ Γ
toΛ = fold (`_ , λ where
  (inl (t , u , tt)) → t · u
  (inr (t , tt))     → ƛ t)

fromΛ : Λ Γ → Term Γ
fromΛ (` x)   = ` x
fromΛ (t · u) = fromΛ t ·′ fromΛ u
fromΛ (ƛ t)   = ƛ′ fromΛ t

fromΛ-toΛ : (t : Term Γ)
  → (fromΛ ∘ toΛ) t ≡ t
fromΛ-toΛ (` x)    = refl
fromΛ-toΛ (t ·′ u) = cong₂ _·′_ (fromΛ-toΛ t) (fromΛ-toΛ u)
fromΛ-toΛ (ƛ′ t)   = cong ƛ′_ (fromΛ-toΛ t)

toΛ-fromΛ : (t : Λ Γ)
  → (toΛ ∘ fromΛ) t ≡ t
toΛ-fromΛ (` x)   = refl
toΛ-fromΛ (t · u) = cong₂ _·_ (toΛ-fromΛ t) (toΛ-fromΛ u)
toΛ-fromΛ (ƛ t)   = cong ƛ_ (toΛ-fromΛ t)
