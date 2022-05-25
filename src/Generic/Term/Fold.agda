open import Prelude

open import Generic.Signature

module Generic.Term.Fold (Ds : ConDs) where

open import Generic.Algebra
open import Generic.Term.Base Ds

private
  variable
    Γ Δ  : Type

module _ {T : Type → Type} (α : (Ds -RawAlg) T) where
  open _-RawAlg α

  mutual
    {-# TERMINATING #-}
    -- This passes the termination checker with `--with-K`, see
    -- https://github.com/agda/agda/issues/4527
    fold : Term Γ → T Γ
    fold (`  x) = var x
    fold (op x) = alg (mapFold Ds x)

    mapFold : (Ds′ : ConDs) → ⟦ Ds′ ⟧ Term Γ → ⟦ Ds′ ⟧ T Γ
    mapFold (D ∷ [])         x       = mapFoldᶜ D x
    mapFold (D ∷ Ds@(_ ∷ _)) (inl x) = inl (mapFoldᶜ D x)
    mapFold (D ∷ Ds@(_ ∷ _)) (inr x) = inr (mapFold Ds x)

    mapFoldᶜ : (D : ConD) → ⟦ D ⟧ᶜ Term Γ → ⟦ D ⟧ᶜ T Γ
    mapFoldᶜ ι       _       = tt
    mapFoldᶜ (σ A D) (a , x) = a , mapFoldᶜ (D a) x
    mapFoldᶜ (ρ R D) (x , y) = mapFoldʳ R x , mapFoldᶜ D y

    mapFoldʳ : (R : RecD) → ⟦ R ⟧ʳ Term Γ → ⟦ R ⟧ʳ T Γ
    mapFoldʳ ι     x  = fold x
    mapFoldʳ (δ R) x  = mapFoldʳ R x
