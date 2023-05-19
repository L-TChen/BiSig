{-# OPTIONS --with-K --safe #-}

open import Prelude
  hiding (_++_)
open import Syntax.Simple.Description

module Syntax.Simple.Association (D : Desc) where

open import Syntax.Simple.Term       D
open Equivalence

private variable
  n m l k : ℕ
  
data AList : (m n : ℕ) → Set where
  []    : AList n n
  _/_∷_ : (t : Tm m) (x : Fin (suc m)) (σ : AList m n) → AList (suc m) n

_/_∷′_ : Tm m → Fin (suc m) → ∃ (AList m) → ∃ (AList (suc m))
t / x ∷′ (n , σ) = n , (t / x ∷ σ)

infixr 5 _++_ 
_++_ : AList m n → AList n l → AList m l
[]           ++ σ₂ = σ₂
(t / x ∷ σ₁) ++ σ₂ = t / x ∷ (σ₁ ++ σ₂)

toSub : AList m n → Sub m n
toSub []          = id
toSub (t / x ∷ ρ) = t for x ⨟ toSub ρ

DecMinₐ : (P : 𝐘 {_} {Sub} m) → Set
DecMinₐ P = (∃₂ λ n σ → Min P n (toSub σ)) ⊎ ¬′ P

DecMin⇔ : {P Q : 𝐘 {_} {Sub} m}
  → P ≗ Q → DecMinₐ P
  → DecMinₐ Q
DecMin⇔ P=Q (inl (_ , σ , Pσ , minPσ)) = inl (_ , σ , P=Q (toSub σ) .to Pσ ,
  λ ρ Qρ → minPσ ρ (P=Q _ .from Qρ))
DecMin⇔ P=Q (inr ¬P) = inr λ Qσ → ¬P (P=Q _ .from Qσ) 

/∷-inv
  : {t u : Tm m} {x y : Fin (suc m)} {σ ρ : AList m n}
  → t / x ∷ σ ≡ u / y ∷ ρ
  → t ≡ u × x ≡ y × σ ≡ ρ
/∷-inv refl = refl , refl , refl

------------------------------------------------------------------------------
-- Association list implies the inequality relation

AList→≥ : AList m n → m ≥ n
AList→≥ []           = ≤-refl
AList→≥ (t / x ∷ ge) = ≤-step (AList→≥ ge)
------------------------------------------------------------------------------
-- Associativity of ++ 

++-assoc
  : (σ₁ : AList m n) {σ₂ : AList n l} {σ₃ : AList l k}
  → (σ₁ ++ σ₂) ++ σ₃ ≡ σ₁ ++ (σ₂ ++ σ₃)
++-assoc []                     = refl
++-assoc (t / x ∷ σ₁) {σ₂} {σ₃} = cong (t / x ∷_) (++-assoc σ₁)

------------------------------------------------------------------------------
-- Basic Properties of AList

++-idᵣ : (σ : AList m n)
  → σ ++ [] ≡ σ
++-idᵣ []          = refl
++-idᵣ (t / x ∷ σ) = begin
  (t / x ∷ σ) ++ []
    ≡⟨⟩
  (t / x ∷ σ ++ [])
    ≡⟨ cong (t / x ∷_) (++-idᵣ σ) ⟩
  (t / x ∷ σ)
    ∎
  where open ≡-Reasoning

instance
  AListIsCategory : IsCategory ℕ AList
  AListIsCategory .id      = []
  AListIsCategory ._⨟_     = _++_
  AListIsCategory .⨟-assoc σ₁ _ _ = ++-assoc σ₁
  AListIsCategory .⨟-idᵣ          = ++-idᵣ
  AListIsCategory .⨟-idₗ σ        = refl

------------------------------------------------------------------------------
-- toSub is a functor

open ≡-Reasoning

toSub-++
  : (σ : AList m n) (ρ : AList n l)
  → toSub (σ ++ ρ) ≡ toSub σ ⨟ toSub ρ
toSub-++ []          ρ = sym $ ⨟-idₗ (toSub ρ)
toSub-++ (t / x ∷ σ) ρ = begin
  toSub ((t / x ∷ σ) ++ ρ)
    ≡⟨⟩
  t for x ⨟ toSub (σ ++ ρ)
    ≡⟨ cong (t for x ⨟_) (toSub-++ σ ρ)  ⟩
  t for x ⨟ (toSub σ ⨟ toSub ρ)
    ≡⟨ sym $ ⨟-assoc (t for x) _ _ ⟩
  (t for x ⨟ toSub σ) ⨟ toSub ρ
    ∎

instance
  TmAListIsPresheaf : IsPresheaf Tm
  TmAListIsPresheaf ._⟨_⟩ t σ   = t ⟨ toSub σ ⟩
  TmAListIsPresheaf .⟨⟩-id t    = ⟨⟩-id ⦃ r = TmSubIsPresheaf ⦄ t
  TmAListIsPresheaf .⟨⟩-⨟ σ ρ t = begin
    t ⟨ toSub (σ ++ ρ) ⟩
      ≡⟨ cong (t ⟨_⟩) (toSub-++ σ ρ) ⟩
    t ⟨ toSub σ ⨟ toSub ρ ⟩
      ≡⟨ ⟨⟩-⨟ (toSub σ) (toSub ρ) t ⟩
    t ⟨ toSub σ ⟩ ⟨ toSub ρ ⟩
      ∎

  TmsAListIsPresheaf : IsPresheaf (λ m → Tm m ^ l)
  TmsAListIsPresheaf ._⟨_⟩  ts σ   = ts ⟨ toSub σ ⟩
  TmsAListIsPresheaf .⟨⟩-id []       = refl
  TmsAListIsPresheaf .⟨⟩-id (t ∷ ts) =
    cong₂ _∷_ (⟨⟩-id ⦃ r = TmSubIsPresheaf ⦄ t) (⟨⟩-id ⦃ r = TmsAListIsPresheaf ⦄ ts)
  TmsAListIsPresheaf .⟨⟩-⨟ σ ρ []       = refl
  TmsAListIsPresheaf .⟨⟩-⨟ σ ρ (t ∷ ts) = cong₂ _∷_ (⟨⟩-⨟ σ ρ t) (⟨⟩-⨟ σ ρ ts)
