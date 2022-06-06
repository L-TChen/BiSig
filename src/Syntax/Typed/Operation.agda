open import Prelude
import Syntax.Simple.Description as S
import Syntax.Typed.Description  as Typed

module Syntax.Typed.Operation {SD : S.Desc} (D : Typed.Desc SD) where
open Typed SD
open import Syntax.Simple.Term SD
  using ()
  renaming (Tm₀ to T)
open import Syntax.Simple.Operation as S

open import Syntax.Typed.Context T
  renaming (_≟_ to _≟ᵢ_)
open import Syntax.Typed.Term D

private
  variable
    A B   : T
    Γ Δ Ξ : Ctx

open DecEq SD ⊥ (λ ()) 
  using ()
  renaming (_≟_ to _≟T_)

mutual
  _≟_ : (t u : Tm A Γ) → Dec (t ≡ u)
  ` x  ≟ ` y  with x ≟ᵢ y
  ... | yes p = yes (cong `_ p)
  ... | no ¬p = no λ where refl → ¬p refl
  op t ≟ op u with compareMap _ t u
  ... | yes p = yes (cong op p)
  ... | no ¬p = no λ where refl → ¬p refl
  ` _  ≟ op _ = no λ ()
  op _ ≟ ` _  = no λ ()

  compareMap : ∀ D → (t u : (⟦ D ⟧ Tm) A Γ) → Dec (t ≡ u)
  compareMap (n ∙ ns) (inl t) (inl u) with compareMapᶜ n t u
  ... | yes p = yes (cong inl p)
  ... | no ¬p = no λ where refl → ¬p refl
  compareMap (_ ∙ ns) (inr t) (inr u) with compareMap ns t u 
  ... | yes p = yes (cong inr p)
  ... | no ¬p = no λ where refl → ¬p refl
  compareMap (n ∙ ns) (inl _) (inr _) = no λ ()
  compareMap (n ∙ ns) (inr _) (inl _) = no λ ()

  compareMapᶜ : (D : ConD Ξ) → (t u : (⟦ D ⟧ᶜ Tm) A Γ) → Dec (t ≡ u)
  compareMapᶜ (ι A D) (refl , t) (refl , u) with compareMapᵃˢ D t u
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes p = yes (cong₂ _,_ refl p)
  compareMapᶜ (σ D)   (A , t)    (B , u) with A ≟T B -- we use the decidable eqaulity on T here
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with compareMapᶜ (D A) t u 
  ... | no ¬q = no λ where refl → ¬q refl
  ... | yes q = yes (cong (A ,_) q)

  compareMapᵃˢ : (D : ArgsD Ξ) → (t u : (⟦ D ⟧ᵃˢ Tm) Γ) → Dec (t ≡ u)
  compareMapᵃˢ ι        _        _        = yes refl
  compareMapᵃˢ (ρ D Ds) (t , ts) (u , us) with compareMapᵃ D t u
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes p with compareMapᵃˢ Ds ts us
  ... | no ¬q = no λ where refl → ¬q refl
  ... | yes q = yes (cong₂ _,_ p q)

  compareMapᵃ : (D : ArgD Ξ) → (t u : (⟦ D ⟧ᵃ Tm) Γ) → Dec (t ≡ u)
  compareMapᵃ (∅     , B) t u = t ≟ u
  compareMapᵃ (A ∙ Δ , B) t u = compareMapᵃ (Δ , B) t u