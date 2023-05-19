{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description as S

module Theory.Annotatability.Term {SD : S.Desc} where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tms to TExps; Sub to TSub)
open import Syntax.Context SD

open import Syntax.Typed.Description    SD as T
open import Syntax.BiTyped.Description  SD as B

open import Syntax.Typed.Intrinsic.Functor   as T
open import Syntax.BiTyped.Intrinsic.Functor as B

open import Theory.Erasure.Description

open import Theory.Annotatability.Description SD

private variable
  mod : Mode
  n m : ℕ
  σ     : TSub n m
  A B C : TExp n
  Γ Δ   : Cxt n

module _ (BD : B.Desc) (TD : T.Desc) (s : Annotatability BD TD) where mutual
  open import Syntax.Typed.Intrinsic.Term   TD
  open import Syntax.BiTyped.Intrinsic.Term BD
    renaming (Tm to BTm)

  annotate
    :          Tm  m     A Γ
    → ∃[ mod ] BTm m mod A Γ
  annotate (` x)        = Infer , ` x
  annotate (op (i , r)) = _ , op (_ , annotateᶜ (proj₂ (s i)) r)

  annotateᶜ : ∀ {D D′} → eraseᶜ D′ ≡ D
    → T.⟦ D ⟧ᶜ (Tm m) A Γ
    → B.⟦ D′ ⟧ᶜ (BTm m) (D′ .ConD.mode) A Γ
  annotateᶜ refl (σ , A=B , ts) = refl , σ , A=B , annotateMap _ _ refl ts

  annotateMap : (D : T.ArgsD n) (D′ : B.ArgsD n) → eraseᵃˢ D′ ≡ D
    → T.⟦ D  ⟧ᵃˢ (Tm  m) σ Γ
    → B.⟦ D′ ⟧ᵃˢ (BTm m) σ Γ
  annotateMap []      []                refl _        = _
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