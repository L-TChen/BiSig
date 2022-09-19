open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Theory.RawAnnotatability {SD : S.Desc} (Id : Set) (D : B.Desc {SD}) where

open B {SD}

open import Syntax.Context
open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tms to TExps)

open import Syntax.BiTyped.Raw.Functor       {SD} Id as M
open import Syntax.BiTyped.RawNoMode.Functor {SD} Id as R
open import Syntax.BiTyped.Raw.Term          {SD} Id D
  renaming (Raw to MRaw)
open import Syntax.BiTyped.RawNoMode.Term    {SD} Id D

private variable
  mod   : Mode
  Ξ n m : ℕ

mutual
  annotateRaw
    : Raw m
    → ∃[ n ] (m ≤ n) × ∃[ mod ] MRaw n mod
  annotateRaw {m} (` x)   = m , ≤-refl  , Infer , ` x
  annotateRaw {m} (t ⦂ A) with annotateRaw t
  ... | n , p , Check , t′ = n , p , Infer , (t′   ⦂ wk p A)
  ... | n , p , Infer , t′ = n , p , Infer , (t′ ↑ ⦂ wk p A)
  annotateRaw {m} (op (D@(ι mod B Ds) , i , ts)) =
    let n , le , ts′ = annotateRawⁿ Ds ts
    in n , le , mod , op (D , i , refl , ts′)

  annotateRawⁿ : (Ds : ArgsD Ξ)
    → R.⟦ Ds ⟧ᵃˢ Raw m
    → ∃[ n ] (m ≤ n) × M.⟦ Ds ⟧ᵃˢ MRaw n
  annotateRawⁿ {Ξ} {m} ∅                     _ = m , ≤-refl , _
  annotateRawⁿ {Ξ} {m} (Θ B.⊢[ mod ] A ∙ Ds) (t , ts) with annotateRawᵃ Θ mod t | annotateRawⁿ Ds ts
  ... | n₁ , less-than-or-equal {k₁} refl , t′ | n₂ , less-than-or-equal {k₂} refl , ts′ =
    m + k₂ + k₁ , m≤m+a+b , {!!} , twkⁿ (less-than-or-equal refl) ts′

  annotateRawᵃ : (Θ : TExps n) (mod : Mode)
    → R.⟦ Θ ⟧ᵃ Raw m
    → ∃[ n ] (m ≤ n) × M.⟦ Θ ⟧ᵃ MRaw n mod
  annotateRawᵃ ∅       mod t with annotateRaw t
  annotateRawᵃ ∅ Check t | n , le , Check , t′ = n , le , t′
  annotateRawᵃ ∅ Check t | n , le , Infer , t′ = n , le , t′ ↑
  annotateRawᵃ ∅ Infer t | n , le , Check , t′ =
    suc n , ≤-step le , (twk (≤-step ≤-refl) t′ ⦂ ` fromℕ n)
  annotateRawᵃ ∅ Infer t | n , le , Infer , t′ = n , le , t′
  annotateRawᵃ (A ∙ Θ) mod (x , t) =
    let n , le , t′ = annotateRawᵃ Θ mod t
    in n , le , x , t′
