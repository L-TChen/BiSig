{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Theory.RawAnnotatability {SD : S.Desc} (Id : Set) (D : B.Desc SD) where

open B SD

open import Syntax.Context     SD
open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tms to TExps)

open import Syntax.BiTyped.Raw.Functor       SD Id as M
open import Syntax.BiTyped.RawNoMode.Functor {SD} Id as R
open import Syntax.BiTyped.Raw.Term          {SD} Id D
  renaming (Raw to MRaw)
open import Syntax.BiTyped.RawNoMode.Term    {SD} Id D

private variable
  mod   : Mode
  Ξ n m : ℕ

module _ where
  open ≡-Reasoning
  m≤m+a+b : {m a b : ℕ}
    → m ≤ m + a + b
  m≤m+a+b {m} {a} {b} = less-than-or-equal {m} {m + a + b} {a + b} $ begin
    m + (a + b)
      ≡⟨ sym (+-assoc m a b) ⟩
    m + a + b
    ∎

toCheck : MRaw m mod
  → MRaw m Check
toCheck {_} {Check} t = t
toCheck {_} {Infer} t = t ↑

cast : MRaw m mod
  → (mod′ : Mode)
  → MRaw (suc m) mod′ ⊎ MRaw m mod′
cast             t Check = inr (toCheck t)
cast {_} {Infer} t Infer = inr t
cast {_} {Check} t Infer = inl (twkˡ (≤-step ≤-refl) t ⦂ ` fromℕ _)

-- For a term with n many type variables, the index of the newly generated type variable is `suc n`.
mutual
  annotateRaw
    : Raw m
    → ∃[ n ] (m ≤ n) × ∃[ mod ] MRaw n mod
  annotateRaw (` x)   = _ , ≤-refl  , Infer , ` x
  annotateRaw (t ⦂ A) with annotateRaw t
  ... | n , p , mod , t′ = n , p , Infer , (toCheck t′ ⦂ wk≤ˡ p A)
  annotateRaw (op (i , ts)) =
    let n , le , ts′ = annotateRawⁿ _ ts
    in n , le , _ , op (i , refl , ts′)

  annotateRawⁿ : (Ds : ArgsD Ξ)
    → R.⟦ Ds ⟧ᵃˢ (Raw m)
    → ∃[ n ] (m ≤ n) × M.⟦ Ds ⟧ᵃˢ (MRaw n)
  annotateRawⁿ         []                    _ = _ , ≤-refl , _
  annotateRawⁿ {m = m} (Θ B.⊢[ mod ] A ∷ Ds) (t , ts) with annotateRawᵃ Θ mod t | annotateRawⁿ Ds ts
  ... | n₁ , less-than-or-equal {k₁} refl , t′ | n₂ , less-than-or-equal {k₂} refl , ts′ =
    m + k₁ + k₂ , m≤m+a+b , twkˡᵃ (less-than-or-equal refl) t′ , twkᵐⁿ m k₁ ts′

  annotateRawᵃ : (Θ : TExps n) (mod : Mode)
    → R.⟦ Θ ⟧ᵃ (Raw m)
    → ∃[ n ] (m ≤ n) × M.⟦ Θ ⟧ᵃ (MRaw n mod)
  annotateRawᵃ [] mod t with annotateRaw t
  ... | n , p , mod′ , t with cast t mod
  ... | inl tₗ = suc n , ≤-step p , tₗ
  ... | inr tᵣ = n , p , tᵣ
  annotateRawᵃ (A ∷ Θ) mod (x , t) =
    let n , le , t′ = annotateRawᵃ Θ mod t
    in n , le , x , t′
