{-# OPTIONS --safe #-}

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Theory.Bidirectionalisation {SD : S.Desc} (BD : B.Desc SD) where

open import Prelude

open B SD

open import Syntax.Typed.Raw.Functor               SD as T
open import Syntax.BiTyped.Pre.Generalised.Functor SD as P

open import Theory.Erasure.Description

open import Syntax.Typed.Raw.Term        (erase BD)
open import Syntax.BiTyped.Pre.Term             BD
open import Syntax.BiTyped.Pre.Generalised.Term BD
open import Theory.Pre.Term                     BD

private variable
  n Ξ : ℕ

mutual

  bidirectionalise? : (d : Mode) (r : Raw n) → ∃[ v ] ∃[ e ] Pre? v e d r
  bidirectionalise? d   r with bidirectionalise' r
  bidirectionalise? Chk r | inl               t     = _ , _ ,    t ↑
  bidirectionalise? Inf r | inl               t     = _ , _ ,    t
  bidirectionalise? Chk r | inr (inl          t   ) = _ , _ ,    t
  bidirectionalise? Inf r | inr (inl          t   ) = _ , _ , ?∋ t
  bidirectionalise? Chk r | inr (inr (_     , t  )) = _ , _ ,    t
  bidirectionalise? Inf r | inr (inr (false , t ↑)) = _ , _ ,    t
  bidirectionalise? Inf r | inr (inr (true  , t  )) = _ , _ , ?∋ t

  bidirectionalise'
    : (r : Raw n)
    →        Pre? true  true Inf r
    ⊎        Pre? true  true Chk r
    ⊎ ∃[ e ] Pre? false e    Chk r  -- implies ∃[ e ] Pre? false e Inf r
  bidirectionalise' (` i)   = inl (` i)
  bidirectionalise' (A ∋ r) with bidirectionalise? Chk r
  ... | false , _ , p = inr (inr (_ , (A ∋ p) ↑))
  ... | true  , _ , p = inl (          A ∋ p    )
  bidirectionalise' (op (i , rs)) with bidirectionaliseᶜ (BD .rules i) rs
  ... | false , Chk , p = inr (inr (_ , op (refl , p)  ))
  ... | false , Inf , p = inr (inr (_ , op (refl , p) ↑))
  ... | true  , Chk , p = inr (inl (    op (refl , p)  ))
  ... | true  , Inf , p = inl (         op (refl , p)   )

  bidirectionaliseᶜ
    : (D : ConD) (rs : T.⟦ eraseᶜ D ⟧ᶜ Raw n)
    → ∃[ v ] ∃[ d ] P.⟦ D ⟧ᶜ Raw Pre? v d rs
  bidirectionaliseᶜ (ι d _ Ds) rs with bidirectionaliseᵃˢ Ds rs
  ... | vs , v , a , p = v , d , vs , a , refl , p

  bidirectionaliseᵃˢ
    : (Ds : ArgsD Ξ)  (rs : T.⟦ eraseᵃˢ Ds ⟧ᵃˢ Raw n)
    → ∃[ vs ] ∃[ v ] And (toList vs) v × P.⟦ Ds ⟧ᵃˢ Raw Pre? vs rs
  bidirectionaliseᵃˢ []                  _        = _ , _ , nil , tt
  bidirectionaliseᵃˢ ((Δ ⊢[ d ] _) ∷ Ds) (r , rs)
      with bidirectionalise? d r | bidirectionaliseᵃˢ Ds rs
  ... | false , _ , p | vs , v , _ , q = false ∷ vs , false , hd   , (_ , p) , q
  ... | true  , _ , p | vs , v , a , q = true  ∷ vs , v     , tl a , (_ , p) , q

bidirectionalise : (d : Mode) (r : Raw n) → Dec (Pre d r)
bidirectionalise d r with bidirectionalise? d r
... | false , _ , p = no (to¬Pre p)
... | true  , _ , p = yes (toPre p)
