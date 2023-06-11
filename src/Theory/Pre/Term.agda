{-# OPTIONS --safe #-}

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Theory.Pre.Term {SD : S.Desc} (BD : B.Desc SD) where

open import Prelude

open import Syntax.Simple SD
open B SD

import Syntax.BiTyped.Pre.Functor             SD as P
import Syntax.BiTyped.Pre.Generalised.Functor SD as G

open import Theory.Erasure

open import Syntax.Typed.Raw             (erase BD)

open import Syntax.BiTyped.Pre.Term             BD
open import Syntax.BiTyped.Pre.Generalised.Term BD

private variable
  v e : Bool
  d   : Mode
  n Ξ : ℕ
  r   : Raw n

mutual

  toPre : Pre? true e d r → Pre d r
  toPre (` i)         = ` i
  toPre (A ∋ p)       = A ∋ toPre p
  toPre (p ↑)         = toPre p ↑
  toPre (op (_ , ps)) = op (toPreᶜ (BD .rules _) ps)

  toPreᶜ : (D : ConD) {rs : R.⟦ eraseᶜ D ⟧ᶜ Raw n}
         → G.⟦ D ⟧ᶜ Raw Pre? true d rs
         → P.⟦ D ⟧ᶜ Raw Pre d rs
  toPreᶜ (ι _ _ Ds) (vs , a , deq , ps) = deq , toPreᵃˢ Ds vs a ps

  toPreᵃˢ : (Ds : ArgsD Ξ) {rs : R.⟦ eraseᵃˢ Ds ⟧ᵃˢ Raw n}
          → (vs : Vec Bool (length Ds)) → And (toList vs) true
          → G.⟦ Ds ⟧ᵃˢ Raw Pre? vs rs
          → P.⟦ Ds ⟧ᵃˢ Raw Pre     rs
  toPreᵃˢ []                  _            _      _              = _
  toPreᵃˢ ((Δ ⊢[ _ ] _) ∷ Ds) (.true ∷ vs) (tl a) ((_ , p) , ps) =
    toPre p , toPreᵃˢ Ds vs a ps

to¬Pre-Inf : Pre? v true Chk r → ¬ Pre Inf r
to¬Pre-Inf (op (_ , _ , _ , d≡Chk , _)) (op (d≡Inf , _)) = Chk≢Inf (trans (sym d≡Chk) d≡Inf)

mutual

  to¬Pre-Chk : Pre? false true Inf r → ¬ Pre Chk r
  to¬Pre-Chk (A ∋ p) ((.A ∋ q) ↑) = to¬Pre p q
  to¬Pre-Chk (op (_ , ps)) (op qs ↑) = to¬Preᶜ (BD .rules _) ps qs
  to¬Pre-Chk (op (_ , _ , _ , d≡Inf , _)) (op (d≡Chk , _)) = Chk≢Inf (trans (sym d≡Chk) d≡Inf)

  to¬Pre : Pre? false e d r → ¬ Pre d r
  to¬Pre (A ∋ p)       (.A ∋ q) = to¬Pre p q
  to¬Pre (p ↑)         q        = to¬Pre-Chk p q
  to¬Pre (?∋ p)        q        = to¬Pre-Inf p q
  to¬Pre (op (_ , ps)) (op qs)  = to¬Preᶜ (BD .rules _) ps qs
  to¬Pre (op (_ , _ , _ , d≡Chk , _)) (op (d≡Inf , _) ↑) = Chk≢Inf (trans (sym d≡Chk) d≡Inf)

  to¬Preᶜ
    : (D : ConD) {rs : R.⟦ eraseᶜ D ⟧ᶜ Raw n}
    →   G.⟦ D ⟧ᶜ Raw Pre? false d rs
    → ¬ P.⟦ D ⟧ᶜ Raw Pre        d rs
  to¬Preᶜ (ι _ _ Ds) (vs , a , _ , ps) (_ , qs) = to¬Preᵃˢ Ds vs a ps qs

  to¬Preᵃˢ
    : (Ds : ArgsD Ξ) {rs : R.⟦ eraseᵃˢ Ds ⟧ᵃˢ Raw n}
    → (vs : Vec Bool (length Ds)) → And (toList vs) false
    →   G.⟦ Ds ⟧ᵃˢ Raw Pre? vs rs
    → ¬ P.⟦ Ds ⟧ᵃˢ Raw Pre     rs
  to¬Preᵃˢ []       []        ()     _              _
  to¬Preᵃˢ (_ ∷ Ds) (._ ∷ vs)  hd    ((_ , p) , ps) (q , qs) = to¬Pre p q
  to¬Preᵃˢ (_ ∷ Ds) (._ ∷ vs) (tl a) ((_ , p) , ps) (q , qs) = to¬Preᵃˢ Ds vs a ps qs
