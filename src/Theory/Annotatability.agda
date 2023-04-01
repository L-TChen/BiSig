{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description as S

module Theory.Annotatability {SD : S.Desc} where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tms to TExps; Sub to TSub)
open import Syntax.Context SD

open import Syntax.Typed.Description    {SD} as T
open import Syntax.BiTyped.Description  {SD} as B

open import Syntax.Typed.Intrinsic.Functor    as T
open import Syntax.BiTyped.Intrinsic.Functor  as B

open import Theory.Erasure.Description

private variable
  mod : Mode
  n m : ℕ
  σ     : TSub n m
  A B C : TExp n
  Γ Δ   : Cxt n

-- -- A bidirectional typing annotates a base typing if every typing rule in the base typing
-- -- has a corresponding typing rule.
Annotatability : (BD : B.Desc) (TD : T.Desc) → Set
Annotatability BD TD = {D : T.ConD} → D ∈ TD → ∃[ D′ ] (D′ ∈ BD × eraseᶜ D′ ≡ D)

module _ (BD : B.Desc) (TD : T.Desc) (s : Annotatability BD TD) where mutual
  open import Syntax.Typed.Intrinsic.Term   TD
  open import Syntax.BiTyped.Intrinsic.Term BD
    renaming (Tm to BTm)

  annotate
    :          Tm  m     A Γ
    → ∃[ mod ] BTm m mod A Γ
  annotate (` x)  = Infer , ` x
  annotate (op (D , i , σ , B=A , ts)) with s i
  ... | ι mod B _ , j , refl = mod , op (_ , j , refl , σ , B=A , annotateMap _ _ refl ts)

  annotateMap : (D  : T.ArgsD n) (D′ : B.ArgsD n) → eraseᵃˢ D′ ≡ D
    → T.⟦ D  ⟧ᵃˢ (Tm  m) σ Γ
    → B.⟦ D′ ⟧ᵃˢ (BTm m) σ Γ
  annotateMap []        []                refl _        = _
  annotateMap (_ ∷ _) (Θ ⊢[ m ] C ∷ Ds) refl (t , ts) =
    annotateMapᵃ Θ m t , annotateMap _ Ds refl ts

  annotateMapᵃ : (Θ : TExps n)
    → (mod : Mode)
    → T.⟦ Θ ⟧ᵃ (Tm m A)      σ Γ
    → B.⟦ Θ ⟧ᵃ (BTm m mod A) σ Γ
  annotateMapᵃ []       m t with annotate t
  annotateMapᵃ [] Check t | Check , t′ = t′
  annotateMapᵃ [] Infer t | Check , t′ = _ ∋ t′
  annotateMapᵃ [] Check t | Infer , t′ = ⇉ t′ by refl
  annotateMapᵃ [] Infer t | Infer , t′ = t′
  annotateMapᵃ (_ ∷ Θ) m t = annotateMapᵃ Θ m t
