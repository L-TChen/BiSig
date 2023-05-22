{-# OPTIONS --with-K --safe #-}

open import Prelude
  hiding (_++_; _+_)
open import Syntax.Simple.Description

module Syntax.Simple.Unification.Properties (D : Desc) where

open import Syntax.Simple.Term        D
open import Syntax.Simple.Association D
open import Syntax.Simple.Unification D
open import Syntax.Simple.Properties  D

open ≡-Reasoning
open Equivalence

private variable
  m n o l k : ℕ
  t u     : Tm m
  i j     : k ∈ D
  ts us   : Tm m ^ k
  x y     : Fin m
  
---------------------------------------------------------------------------
-- Variable Elimination Lemma

module Variable-Elimination (σ : Sub (suc m) n) (x : Fin (suc m)) (t : Tm m) where
  helper
    : (y : Fin (suc m))
    → lookup (t for x ⨟ tabulate (lookup σ ∘ punchIn x)) y
      ≡ sub-for t x y ⟨ tabulate (`_ ∘ punchIn x) ⟩ ⟨ σ ⟩
  helper y = begin
    lookup (t for x ⨟ tabulate (lookup σ ∘ punchIn x)) y
      ≡⟨⟩
    lookup (tabulate λ i → lookup (t for x) i ⟨ tabulate (lookup σ ∘ punchIn x) ⟩) y
      ≡⟨ lookup∘tabulate (_⟨ tabulate (lookup σ ∘ punchIn x) ⟩ ∘ lookup (t for x)) y ⟩
    lookup (t for x) y ⟨ tabulate (lookup σ ∘ punchIn x) ⟩
      ≡⟨ cong _⟨ tabulate (lookup σ ∘ punchIn x) ⟩ (lookup∘tabulate (sub-for t x) y) ⟩
    sub-for t x y ⟨ tabulate (lookup σ ∘ punchIn x) ⟩
      ≡⟨ cong (sub-for t x y ⟨_⟩)
        (tabulate-cong (λ i → cong (_⟨ σ ⟩) (sym $ lookup∘tabulate (`_ ∘ punchIn x) i))) ⟩
    sub-for t x y ⟨ tabulate (`_ ∘ punchIn x) ⨟ σ ⟩ 
      ≡⟨ ⟨⟩-⨟ (tabulate (`_ ∘ punchIn x)) σ (sub-for t x y) ⟩
    sub-for t x y ⟨ tabulate (`_ ∘ punchIn x) ⟩ ⟨ σ ⟩
      ∎
   
  var-elim-pointwise
    : (` x ≈ punchInTm x t) _ σ
    → (y : Fin (suc m))
    → lookup (t for x ⨟ tabulate (lookup σ ∘ punchIn x)) y ≡ lookup σ y
  var-elim-pointwise eq y with x ≟ y
  ... | yes refl = begin
    lookup (t for x ⨟ tabulate (lookup σ ∘ punchIn x)) x
      ≡⟨ helper x ⟩
    sub-for t x x ⟨ tabulate (`_ ∘ punchIn x) ⟩ ⟨ σ ⟩
      ≡⟨ cong (λ t → t ⟨ tabulate _ ⟩ ⟨ σ ⟩) $ sub-t-for-x-x {t = t} {x} ⟩  
    t ⟨ tabulate (`_ ∘ punchIn x) ⟩ ⟨ σ ⟩
      ≡⟨ cong (_⟨ σ ⟩) (rename-is-sub t) ⟩
    t ⟨ punchIn y ⟩ ⟨ σ ⟩
      ≡⟨ sym eq ⟩
    lookup σ x
      ∎
      
  ... | no ¬p    = begin
    lookup (t for x ⨟ tabulate (lookup σ ∘ punchIn x)) y
      ≡⟨ helper y ⟩
    sub-for t x y ⟨ tabulate (`_ ∘ punchIn x) ⟩ ⟨ σ ⟩
      ≡⟨ (cong (λ t → t ⟨ tabulate _ ⟩ ⟨ σ ⟩) $ sub-t-for-x-y ¬p) ⟩
    ` punchOut ¬p ⟨ tabulate (`_ ∘ punchIn x) ⟩ ⟨ σ ⟩
      ≡⟨ cong (_⟨ σ ⟩) (lookup∘tabulate (`_ ∘ punchIn x) _) ⟩
    ` punchIn x (punchOut ¬p) ⟨ σ ⟩
      ≡⟨ cong (lookup σ) (F.punchIn-punchOut ¬p) ⟩
    lookup σ y
      ∎

  var-elim
    : (` x ≈ punchInTm x t) _ σ
    → t for x ⨟ tabulate (lookup σ ∘ punchIn x) ≡ σ 
  var-elim eq = begin
    t for x ⨟ tabulate (lookup σ ∘ punchIn x)
      ≡⟨ (sym $ tabulate∘lookup _) ⟩
    tabulate (lookup (t for x ⨟ tabulate (lookup σ ∘ punchIn x)))
      ≡⟨ tabulate-cong (var-elim-pointwise eq) ⟩
    tabulate (lookup σ)
      ≡⟨ tabulate∘lookup σ ⟩
    σ
      ∎
open Variable-Elimination using (var-elim)

module _ (t u : Tm (suc m)) (x : Fin (suc m)) (r : Tm m) (σ : Sub m n) where
  subst-equiv : (t ⟨ r for x ⟩ ≈ u ⟨ r for x ⟩ [ σ ⨟]) ≗ (t ≈ u [ r for x ⨟ σ ⨟])
  subst-equiv ρ .to   eq = begin
    t ⟨ r for x ⨟ σ ⨟ ρ ⟩
      ≡⟨ t⟨fgh⟩=t⟨f⟩⟨gh⟩ t (r for x) _ _ ⟩
    t ⟨ r for x ⟩ ⟨ σ ⨟ ρ ⟩
      ≡⟨ eq ⟩
    u ⟨ r for x ⟩ ⟨ σ ⨟ ρ ⟩
      ≡⟨ sym (t⟨fgh⟩=t⟨f⟩⟨gh⟩ u (r for x) _ _) ⟩
    u ⟨ r for x ⨟ σ ⨟ ρ ⟩
      ∎

  subst-equiv ρ .from eq = begin
    t ⟨ r for x ⟩ ⟨ σ ⨟ ρ ⟩
      ≡⟨ (sym $ t⟨fgh⟩=t⟨f⟩⟨gh⟩ t (r for x) _ _) ⟩
    t ⟨ r for x ⨟ σ ⨟ ρ ⟩
      ≡⟨ eq ⟩
    u ⟨ r for x ⨟ σ ⨟ ρ ⟩
      ≡⟨ t⟨fgh⟩=t⟨f⟩⟨gh⟩ u (r for x) _ _ ⟩
    u ⟨ r for x ⟩ ⟨ σ ⨟ ρ ⟩
      ∎

-------------------------------------------------------------------------
-- Definitions of Most General Unifier and its variant with an accumulator
-------------------------------------------------------------------------

MGU : (t u : Tm m) →  𝐘 {_} {Sub} m
MGU t u = Min (t ≈ u)

AMGU : (t u : Tm m) (σ : Sub m n) → 𝐘 n
AMGU t u σ = Min (t ≈ u [ σ ⨟])

AMGUⁿ : (ts us : Tm m ^ k) (σ : Sub m n) → 𝐘 n
AMGUⁿ ts us σ = Min (ts ≈ us [ σ ⨟])

DecMGU : (t u : Tm m) → Set
DecMGU t u = DecMinₐ (t ≈ u)

DecAMGU : (t u : Tm m) (σ : AList m n) → Set
DecAMGU t u σ = DecMinₐ $ t ≈ u [ toSub σ ⨟] 

DecAMGUⁿ : (ts us : Tm m ^ k) (σ : AList m n) → Set
DecAMGUⁿ ts us σ = DecMinₐ $ ts ≈ us [ toSub σ ⨟] 

-------------------------------------------------------------------------
-- A Trivial Equivalence
-------------------------------------------------------------------------

module _(t u : Tm m) (ts us : Tm m ^ k) where 
  Tms≈ : (σ : Sub m n) → ((t ∷ ts) ≈ (u ∷ us)) _ σ ⇔ ((t ≈ u) ∧ (ts ≈ us)) _ σ
  Tms≈ σ = ∷-injectivity-⇔ _ _ _ _
    
  MinTms≈ : (σ : Sub m n)
    → Min ((t ∷ ts) ≈ (u ∷ us) [ σ ⨟]) ≗ Min ((t ≈ u) ∧ (ts ≈ us) [ σ ⨟])
  MinTms≈ σ = Min≗ (ext≗ σ Tms≈)
  
----------------------------------------------------------------------
-- Correctness of FlexRigid
----------------------------------------------------------------------

module _ {m : ℕ} {x : Fin (suc m)} {t : Tm (suc m)} (x∉ : x ∉ₜ t) where
  ≈-flexRigid∉ : (` x ≈ t) _ $ punchOutTm x∉ for x
  ≈-flexRigid∉ = begin
    ` x ⟨ (punchOutTm x∉) for x ⟩
      ≡⟨ x⟨t/x⟩=t x ⟩
    punchOutTm x∉
      ≡⟨ sym (punchIn-t⟨u/x⟩=t (punchOutTm x∉)) ⟩
    punchInTm x (punchOutTm x∉) ⟨ (punchOutTm x∉) for x ⟩
      ≡⟨ (cong _⟨ punchOutTm x∉ for x ⟩ $ punchInTm-punchOutTm x∉) ⟩
    t ⟨ (punchOutTm x∉) for x ⟩
      ∎

  flexRigid∉-mgu : Min (` x ≈ t) _ (punchOutTm x∉ for x)
  flexRigid∉-mgu = ≈-flexRigid∉ , λ σ eq →
    tabulate (lookup σ ∘ punchIn x) , (var-elim σ x _ (begin
      ` x ⟨ σ ⟩
        ≡⟨ eq  ⟩
      t ⟨ σ ⟩
        ≡⟨ (sym $ cong _⟨ σ ⟩ $ punchInTm-punchOutTm x∉) ⟩
      punchInTm x (punchOutTm x∉) ⟨ σ ⟩
        ∎))

----------------------------------------------------------------------
-- Correctness of Flex-Rigid/Flex 
----------------------------------------------------------------------
flex-mgu : (x : Fin m) (t : Tm m) → DecMGU (` x) t
flex-mgu {suc m} x t with x ∈ₜ? t
flex-mgu x (` y)     | yes (here refl) = inl (_ , id , Min-id {ℕ} {Sub} (` y ≈ ` y) refl)
flex-mgu x (op′ _ _) | yes x∈ = inr λ where
  {j = σ} eq → op≢var (unify-occur σ x∈  eq)
... | no  x∉ = inl (_ , flex∉ x∉ , Min-⨟-id _ _ (flexRigid∉-mgu x∉))

flex-amgu : (x : Fin m) (t : Tm m) → DecAMGU (` x) t id
flex-amgu x t =  DecMin⇔ (P=Pid⨟- (` x ≈ t)) $ flex-mgu x t 

----------------------------------------------------------------------
-- Correctness of amgu and amguⁿ
----------------------------------------------------------------------

mutual
--  open import Syntax.Simple.Rewrite

  amgu⁺ : (t u : Tm m) (σ : AList m n) → DecAMGU t u σ

  amgu⁺ (` x)      t     []          = flex-amgu x t
  amgu⁺ t          (` y) []          = DecMin⇔ (ext≗ id (≈-sym (` y) t)) $ flex-amgu y t

  amgu⁺ t          u     (r / x ∷ σ) = DecMin⇔
    (subst-equiv t u x r (toSub σ)) $ amgu⁺ (t ⟨ r for x ⟩) (u ⟨ r for x ⟩) σ

  amgu⁺ (op′ i ts) (op′ j us) σ with i ≟∈ j
  ... | no ¬p    = inr λ {_} {ρ} eq → ¬p (op-inj₁₂ eq)
  ... | yes refl =  DecMin⇔ (λ _ → op-cong⇔) $ amguⁿ⁺ ts us σ 

  amguⁿ⁺ : (ts us : Tm m ^ l) (σ : AList m n) → DecAMGUⁿ ts us σ
  amguⁿ⁺ []       []       σ = inl (_ , id , refl , λ ρ _ → ρ , ⨟-idₗ ρ)
  amguⁿ⁺ (t ∷ ts) (u ∷ us) σ with amgu⁺ t u σ
  ... | inr t≉u = inr λ {_} {ρ} eq → t≉u (V.∷-injectiveˡ eq)
  ... | inl (_ , ρ , t≈u) with amguⁿ⁺ ts us (σ ⨟ ρ)
  ... | inr ts≉us           = inr λ {_} {γ} ts≈us →
  -- Liang-Ting (2023-05-16): Is there any better way to treat the following conversion
  -- between toSub (σ ⨟ ρ) = toSub σ ⨟ toSub ρ? 

    failure-propagate {P = t ≈ u} {ts ≈ us} (toSub σ) (toSub ρ) t≈u (λ {_} {γ} eq → ts≉us
        (begin
      ts ⟨ toSub (σ ⨟ ρ) ⨟ γ ⟩
        ≡⟨ cong (λ ρ → ts ⟨ ρ ⨟ γ ⟩) (toSub-++ σ ρ) ⟩
      ts ⟨ toSub σ ⨟ toSub ρ ⨟ γ ⟩
        ≡⟨ eq ⟩
      us ⟨ toSub σ ⨟ toSub ρ ⨟ γ ⟩
        ≡⟨ cong (λ ρ → us ⟨ ρ ⨟ γ ⟩) (sym (toSub-++ σ ρ)) ⟩
      us ⟨ toSub (σ ⨟ ρ) ⨟ γ ⟩
        ∎))
      (V.∷-injective ts≈us)
  ... | inl (_ , γ , ts≈us) = inl (_ , ρ ⨟ γ , (MinTms≈ t u ts us (toSub σ) (toSub $ ρ ⨟ γ) .from goal))
    where
      -- goal = optimist (t ≈ u) (ts ≈ us) (toSub σ) (toSub ρ) (toSub γ) (≈-↑ t u) t≈u ts≈us
      goal′ : Min ((t ≈ u) ∧ (ts ≈ us) [ toSub σ ⨟]) _ ((toSub ρ) ⨟ (toSub γ))
      goal′ = optimist (t ≈ u) (ts ≈ us) (toSub σ) (toSub ρ) (toSub γ) (≈-↑ t u) t≈u
        (subst (λ σ → Min (ts ≈ us [ σ ⨟]) _ (toSub γ)) (toSub-++ σ ρ) ts≈us)

      goal : Min ((t ≈ u) ∧ (ts ≈ us) [ toSub σ ⨟]) _ (toSub (ρ ⨟ γ))
      goal = subst (λ γ → Min ((t ≈ u) ∧ (ts ≈ us) [ toSub σ ⨟]) _ γ) (sym $ toSub-++ ρ γ) goal′

mgu⁺ : (t u : Tm m) → DecMGU t u
mgu⁺ t u = DecMin⇔ (⇔-sym ∘ P=Pid⨟- (t ≈ u)) (amgu⁺ t u [])
