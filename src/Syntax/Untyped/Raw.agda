open import Prelude

-- Id is for the type of identitifers
module Syntax.Untyped.Raw (Id : Set) (_≟_ : (x y : Id) → Dec (x ≡ y)) where

open import Syntax.Untyped.Signature as S
  using (Sig; sig; ∣_∣; arity)

private
  variable
    n m : ℕ
    O   : Set
    X Y : Set ℓ

⟦_⟧ᵇ_ : (a : ℕ) → (X : Set) → Set
⟦ zero ⟧ᵇ  X = X
⟦ suc a ⟧ᵇ X = Id × ⟦ a ⟧ᵇ X

⟦_⟧ᶜ_ : (as : List ℕ) (X : Set) → Set
⟦ []     ⟧ᶜ _ = ⊤
⟦ a ∷ as ⟧ᶜ X = ⟦ a ⟧ᵇ X × ⟦ as ⟧ᶜ X

⟦_⟧_ : (s : Sig O) (X : Set) → Set
⟦_⟧_ {O} (sig ar) X = Σ[ o ∈ O ] ⟦ ar o ⟧ᶜ X

module _ {O} (s : Sig O) where
  open import Syntax.Untyped.Term s as T

  data Raw : Set where
    `_ : Id        → Raw
    op : ⟦ s ⟧ Raw → Raw

  _∙_ : Id → (Id → Fin n) → Id → Fin (suc n)
  (x ∙ ρ) y with x ≟ y
  ... | yes p = zero
  ... | no ¬p = suc (ρ y)
  
  mutual
    alpha : (Id → Fin n)
      → Raw → Tm n 
    alpha ρ (` x)         = ` ρ x
    alpha ρ (op (f , ts)) = op (f , (alphaMapᶜ (arity s f) ρ ts))

    alphaMapᶜ : ∀ as → (Id → Fin n) → ⟦ as ⟧ᶜ Raw → (S.⟦ as ⟧ᶜ Tm) n
    alphaMapᶜ []       ρ _       = _
    alphaMapᶜ (a ∷ as) ρ (t , u) = alphaMapᵇ a ρ t , (alphaMapᶜ as ρ u)

    alphaMapᵇ : ∀ a → (Id → Fin n) → ⟦ a ⟧ᵇ Raw → (S.⟦ a ⟧ᵇ Tm) n
    alphaMapᵇ zero    ρ t        = alpha ρ t
    alphaMapᵇ (suc a) ρ (id , t) = alphaMapᵇ a (id ∙ ρ) t
