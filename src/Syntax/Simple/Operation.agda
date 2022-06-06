open import Prelude
open import Syntax.Simple.Description

module Syntax.Simple.Operation (D : Desc) where

open import Syntax.Simple.Term D

private variable
  A B : Set

freeAlg : (D -Alg) List
var freeAlg x = x ∷ []
alg freeAlg = algᶜ _
  where
    algⁿ : ∀ n → List A ^ n → List A
    algⁿ zero    _        = []
    algⁿ (suc n) (t , ts) = t ++ algⁿ _ ts
    algᶜ : ∀ D → ⟦ D ⟧ List ⇒₁ List
    algᶜ (n ∷ ns) (inl x) = algⁿ n x
    algᶜ (n ∷ ns) (inr y) = algᶜ ns y
fv : Tm ⇒₁ List
fv = fold freeAlg

module DecEq (A : Set) (_≟ᵢ_ : (x y : A) → Dec (x ≡ y)) where mutual
  _≟_ : (t u : Tm A) → Dec (t ≡ u)
  (` x) ≟ (` y) with x ≟ᵢ y
  ... | yes p = yes (cong `_ p)
  ... | no ¬p = no λ where refl → ¬p refl
  op t  ≟ op u  with compareMap _ t u
  ... | yes p = yes (cong op p) 
  ... | no ¬p = no λ where refl → ¬p refl
  (` x) ≟ op u  = no λ ()
  op x  ≟ (` y) = no λ ()

  compareMap : ∀ D → (t u : (⟦ D ⟧ Tm) A) → Dec (t ≡ u)
  compareMap (n ∷ ns) (inl t) (inl u) with compareMapⁿ n t u
  ... | yes p = yes (cong inl p)
  ... | no ¬p = no λ where refl → ¬p refl
  compareMap (n ∷ ns) (inr t) (inr u) with compareMap ns t u 
  ... | yes p = yes (cong inr p)
  ... | no ¬p = no λ where refl → ¬p refl
  compareMap (n ∷ ns) (inl t) (inr u) = no λ ()
  compareMap (n ∷ ns) (inr t) (inl u) = no λ ()

  compareMapⁿ : ∀ n → (ts us : Tm A ^ n) → Dec (ts ≡ us)
  compareMapⁿ zero    _        _        = yes refl
  compareMapⁿ (suc n) (t , ts) (u , us) with t ≟ u
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes p with compareMapⁿ n ts us 
  ... | no ¬q = no λ where refl → ¬q refl
  ... | yes q = yes (cong₂ _,_ p q)