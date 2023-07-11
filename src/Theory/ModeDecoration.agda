import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Theory.ModeDecoration {SD : S.Desc} (BD : B.Desc SD) where

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

  decorate' : (r : Raw n) → ∃[ v ] ∃[ d ] Pre? v true d r
  decorate' (` i) = _ , _ , ` i
  decorate' (A ∋ r) with adjustMode Chk (decorate' r)
  ... | _ , _ , p = _ , _ , A ∋ p
  decorate' (op (i , rs)) with decorateᶜ (BD .rules i) rs
  ... | _ , _ , p = _ , _ , op (refl , p)

  decorateᶜ
    : (D : ConD) (rs : T.⟦ eraseᶜ D ⟧ᶜ Raw n)
    → ∃[ v ] ∃[ d ] P.⟦ D ⟧ᶜ Raw Pre? v d rs
  decorateᶜ (ι d _ Ds) rs with decorateᵃˢ Ds rs
  ... | vs , v , a , p = v , d , vs , a , refl , p

  decorateᵃˢ
    : (Ds : ArgsD Ξ)  (rs : T.⟦ eraseᵃˢ Ds ⟧ᵃˢ Raw n)
    → ∃[ vs ] ∃[ v ] And (toList vs) v × P.⟦ Ds ⟧ᵃˢ Raw Pre? vs rs
  decorateᵃˢ []                  _        = _ , _ , nil , tt
  decorateᵃˢ ((Δ ⊢[ d ] _) ∷ Ds) (r , rs)
      with adjustMode d (decorate' r) | decorateᵃˢ Ds rs
  ... | false , _ , p | vs , v , _ , q = false ∷ vs , false , hd   , (_ , p) , q
  ... | true  , _ , p | vs , v , a , q = true  ∷ vs , v     , tl a , (_ , p) , q

decorate? : (d : Mode) (r : Raw n) → ∃[ v ] ∃[ e ] Pre? v e d r
decorate? d = adjustMode d ∘ decorate'

decorate : (d : Mode) (r : Raw n) → Dec (Pre d r)
decorate d r with decorate? d r
... | false , _ , p = no (to¬Pre p)
... | true  , _ , p = yes (toPre p)
