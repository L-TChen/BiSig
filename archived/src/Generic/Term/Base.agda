open import Prelude

open import Generic.Signature

module Generic.Term.Base (Ds : ConDs) where

open import Generic.Algebra

private
  variable
    Γ Δ  : Type

data Term (Γ : Type) : Type where
  `_ : Γ                   → Term Γ
  op : (t : ⟦ Ds ⟧ Term Γ) → Term Γ

pattern op₁ t = op (inl t)
pattern op₂ t = op (inr t)
pattern op₃ t = op (inr (inr t))
pattern op₄ t = op (inr (inr (inr t)))
