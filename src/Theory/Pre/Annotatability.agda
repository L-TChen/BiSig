import Syntax.Simple.Signature  as S
import Syntax.BiTyped.Signature as B'

module Theory.Pre.Annotatability {SD : S.SigD} (BD : B'.SigD SD) where

open import Prelude

open import Syntax.Simple  SD
open import Syntax.Context SD

open import Theory.Erasure

open import Syntax.Typed.Raw               (erase BD)
open import Syntax.Typed.Raw.Ordering.Term (erase BD)
import      Syntax.Typed.Raw.Ordering.Functor     SD as O

open import Syntax.BiTyped.Pre.Generalised.Term    BD
import      Syntax.BiTyped.Pre.Generalised.Functor SD as G

open import Syntax.Typed.Term (erase BD)
import      Syntax.Typed.Functor     SD as T

open import Syntax.BiTyped.Term    BD
import      Syntax.BiTyped.Functor SD as B
open B' SD

private variable
  Ξ   : ℕ
  v e : Bool
  d   : Mode
  r   : Raw _
  Γ   : Cxt 0
  A   : Ty

mutual

  annotatability
    : Pre? v e d r
    → Γ ⊢ r ⦂ A
    → ∃[ r' ]  r ≤ᴬ r'
            ×  Γ ⊢ r' [ d ] A
  annotatability (` j) (var i eq) = _ , ` j , var i eq
  annotatability (A ∋ p) (.A ∋ t) with annotatability p t
  ... | _ , r≤r' , t' = _ , A ∋ r≤r' , A ∋ t'
  annotatability (p ↑) t with annotatability p t
  ... | _ , r≤r' , t' = _ , r≤r' , t' ↑ refl
  annotatability (?∋ p) t with annotatability p t
  ... | _ , r≤r' , t' = _ , _ ∋⁺ r≤r' , _ ∋ t'
  annotatability (op (_ , ps)) (op ts) with annotatabilityᶜ (BD .ar _) ps ts
  ... | _ , rs≤rs' , ts' = _ , op (refl , rs≤rs') , op ts'

  annotatabilityᶜ
    : (D : OpD) {rs : R.⟦ eraseᶜ D ⟧ᶜ Raw _}
    → G.⟦ D ⟧ᶜ Raw Pre? v d rs
    → T.⟦ eraseᶜ D ⟧ᶜ Raw _⊢_⦂_ Γ rs A
    → ∃[ rs' ] O.⟦ eraseᶜ D , eraseᶜ D ⟧ᶜ Raw _≤ᴬ_ refl rs rs'
             × B.⟦ D ⟧ᶜ Raw _⊢_[_]_ Γ rs' d A
  annotatabilityᶜ (ι _ _ Ds) (vs , a , deq , ps) (σ , σeq , ts)
      with annotatabilityᵃˢ Ds vs ps ts
  ... | _ , rs≤rs' , ts' = _ , rs≤rs' , (deq , σ , σeq , ts')

  annotatabilityᵃˢ
    : (Ds : ArgsD Ξ) {rs : R.⟦ eraseᵃˢ Ds ⟧ᵃˢ Raw _} {σ : TSub Ξ 0}
    → (vs : Vec Bool (length Ds))
    → G.⟦ Ds ⟧ᵃˢ Raw Pre? vs rs
    → T.⟦ eraseᵃˢ Ds ⟧ᵃˢ Raw _⊢_⦂_ σ Γ rs
    → ∃[ rs' ] O.⟦ eraseᵃˢ Ds ⟧ᵃˢ Raw _≤ᴬ_ rs rs'
             × B.⟦ Ds ⟧ᵃˢ Raw _⊢_[_]_ σ Γ rs'
  annotatabilityᵃˢ [] _ _ _ = _ , _ , _
  annotatabilityᵃˢ ((Δ ⊢[ _ ] _) ∷ Ds) (_ ∷ vs) ((_ , p) , ps) (t , ts)
    with annotatabilityᵃ Δ p t | annotatabilityᵃˢ Ds vs ps ts
  ... | _ , r≤r' , t' | _ , rs≤rs' , ts' = _ , (r≤r' , rs≤rs') , (t' , ts')

  annotatabilityᵃ
    : (Δ : TExps Ξ) {r : Raw _} {σ : TSub Ξ 0}
    → Pre? v e d r
    → T.⟦ Δ ⟧ᵃ Raw (_⊢_⦂ A) σ Γ r
    → ∃[ r' ] r ≤ᴬ r'
            × B.⟦ Δ ⟧ᵃ Raw (_⊢_[ d ] A) σ Γ r'
  annotatabilityᵃ []      p t = annotatability    p t
  annotatabilityᵃ (_ ∷ Δ) p t = annotatabilityᵃ Δ p t
