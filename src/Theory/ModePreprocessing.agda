{-# OPTIONS --safe #-}

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Theory.ModePreprocessing {SD : S.Desc} (BD : B.Desc SD) where

open import Prelude

open B SD

open import Syntax.Typed.Raw.Functor               SD as T
open import Syntax.BiTyped.Pre.Generalised.Functor SD as P

open import Theory.Erasure

open import Syntax.Typed.Raw.Term        (erase BD)
open import Syntax.BiTyped.Pre.Term             BD
open import Syntax.BiTyped.Pre.Generalised.Term BD
open import Theory.Pre.Term                     BD

private variable
  n Ξ : ℕ

adjustMode : (d : Mode) {r : Raw n}
           → ∃[ v ] ∃[ d' ] Pre? v true d' r
           → ∃[ v ] ∃[ e  ] Pre? v e    d  r
adjustMode Chk (_ , Chk , p) = _ , _ ,    p
adjustMode Chk (_ , Syn , p) = _ , _ ,    p ↑
adjustMode Syn (_ , Chk , p) = _ , _ , ?∋ p
adjustMode Syn (_ , Syn , p) = _ , _ ,    p

mutual

  preprocess' : (r : Raw n) → ∃[ v ] ∃[ d ] Pre? v true d r
  preprocess' (` i) = _ , _ , ` i
  preprocess' (A ∋ r) with adjustMode Chk (preprocess' r)
  ... | _ , _ , p = _ , _ , A ∋ p
  preprocess' (op (i , rs)) with preprocessᶜ (BD .rules i) rs
  ... | _ , _ , p = _ , _ , op (refl , p)

  preprocessᶜ
    : (D : ConD) (rs : T.⟦ eraseᶜ D ⟧ᶜ Raw n)
    → ∃[ v ] ∃[ d ] P.⟦ D ⟧ᶜ Raw Pre? v d rs
  preprocessᶜ (ι d _ Ds) rs with preprocessᵃˢ Ds rs
  ... | vs , v , a , p = v , d , vs , a , refl , p

  preprocessᵃˢ
    : (Ds : ArgsD Ξ)  (rs : T.⟦ eraseᵃˢ Ds ⟧ᵃˢ Raw n)
    → ∃[ vs ] ∃[ v ] And (toList vs) v × P.⟦ Ds ⟧ᵃˢ Raw Pre? vs rs
  preprocessᵃˢ []                  _        = _ , _ , nil , tt
  preprocessᵃˢ ((Δ ⊢[ d ] _) ∷ Ds) (r , rs)
      with adjustMode d (preprocess' r) | preprocessᵃˢ Ds rs
  ... | false , _ , p | vs , v , _ , q = false ∷ vs , false , hd   , (_ , p) , q
  ... | true  , _ , p | vs , v , a , q = true  ∷ vs , v     , tl a , (_ , p) , q

preprocess? : (d : Mode) (r : Raw n) → ∃[ v ] ∃[ e ] Pre? v e d r
preprocess? d = adjustMode d ∘ preprocess'

preprocess : (d : Mode) (r : Raw n) → Dec (Pre d r)
preprocess d r with preprocess? d r
... | false , _ , p = no (to¬Pre p)
... | true  , _ , p = yes (toPre p)
