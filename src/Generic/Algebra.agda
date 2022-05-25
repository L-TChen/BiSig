open import Prelude
open import Generic.Signature

module Generic.Algebra where

private
  variable
    Γ Δ  : Type

record _-RawAlg (Ds : ConDs) (T : Type → Type) : Type₁ where
  constructor _,_
  field
    var : Γ          → T Γ
    alg : ⟦ Ds ⟧ T Γ → T Γ
