{-# OPTIONS --safe #-}

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Theory.Bidirectionalisation {SD : S.Desc} (BD : B.Desc SD) where

open import Prelude

open B SD

open import Syntax.Typed.Raw.Functor       SD as TF
open import Syntax.BiTyped.HasMode.Functor SD as BF

open import Theory.Erasure.Description

open import Syntax.Typed.Raw.Term (erase BD)
open import Syntax.BiTyped.HasMode.Term  BD

private variable
  n Ξ : ℕ

mutual

  bidirectionalise : (d : Mode) (t : Raw n) → Dec (HasMode d t)
  bidirectionalise d   t with bidirectionalise' t
  bidirectionalise Chk t | inl        Inf-t           = yes (Inf-t ↑)
  bidirectionalise Inf t | inl        Inf-t           = yes  Inf-t
  bidirectionalise Chk t | inr (inl (¬Inf-t , Chk-t)) = yes  Chk-t
  bidirectionalise Inf t | inr (inl (¬Inf-t , Chk-t)) = no  ¬Inf-t
  bidirectionalise Chk t | inr (inr          ¬Chk-t ) = no  ¬Chk-t
  bidirectionalise Inf t | inr (inr          ¬Chk-t ) = no (¬Chk-t ∘ _↑)

  bidirectionalise'
    : (t : Raw n)
    →    HasMode Inf t
    ⊎ (¬ HasMode Inf t × HasMode Chk t)
    ⊎                  ¬ HasMode Chk t  -- implies ¬ HasMode Inf t
  bidirectionalise' (` i) = inl (` i)
  bidirectionalise' (A ∋ t) with bidirectionalise Chk t
  ... | yes t' = inl (A ∋ t')
  ... | no ¬t' = inr (inr λ { ((.A ∋ t') ↑) → ¬t' t' })
  bidirectionalise' (op (i , ts)) with bidirectionaliseᶜ (BD .rules i) ts
  ... | yes (Chk , Chk-ts@(d≡Chk , _)) =
    inr (inl ((λ { (op (d≡Inf , _)) → Chk≢Inf (trans (sym d≡Chk) d≡Inf) }) , op Chk-ts))
  ... | yes (Inf , Inf-ts) = inl (op Inf-ts)
  ... | no ¬ts' = inr (inr λ { (op ts' ↑) → ¬ts' (_ , ts')
                             ; (op ts'  ) → ¬ts' (_ , ts') })

  bidirectionaliseᶜ
    : (D : ConD) (ts : TF.⟦ eraseᶜ D ⟧ᶜ Raw n)
    → Dec (Σ[ d ∈ Mode ] BF.⟦ D ⟧ᶜ (λ k → HasMode {k}) n d ts)
  bidirectionaliseᶜ (ι d _ D) ts with bidirectionaliseᵃˢ D ts
  ... | yes ts' = yes (d , refl , ts')
  ... | no ¬ts' = no λ (_ , _ , ts') → ¬ts' ts'

  bidirectionaliseᵃˢ
    : (D : ArgsD Ξ) (ts : TF.⟦ eraseᵃˢ D ⟧ᵃˢ Raw n)
    → Dec (BF.⟦ D ⟧ᵃˢ (λ k → HasMode {k}) n ts)
  bidirectionaliseᵃˢ []                  _        = yes _
  bidirectionaliseᵃˢ ((Δ ⊢[ d ] _) ∷ Ds) (t , ts) with bidirectionalise d t
  ... | no ¬t' = no λ (t' , _) → ¬t' t'
  ... | yes t' with bidirectionaliseᵃˢ Ds ts
  ...          | yes ts' = yes (t' , ts')
  ...          | no ¬ts' = no λ (_ , ts') → ¬ts' ts'
