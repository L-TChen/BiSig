{-# OPTIONS --with-K  #-}

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
      ≡⟨ (cong (λ t → t ⟨ tabulate _ ⟩ ⟨ σ ⟩) $ sub-t-for-x-x {t = t} {x}) ⟩
    t ⟨ tabulate (`_ ∘ punchIn x) ⟩ ⟨ σ ⟩
      ≡⟨ (cong _⟨ σ ⟩ $ rename-is-sub t) ⟩
    t ⟨ tabulate (punchIn x) ⟩ ⟨ σ ⟩
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

-------------------------------------------------------------------------
-- Definitions of Most General Unifier and its variant with an accumulator
-------------------------------------------------------------------------

MGU : (t u : Tm m) →  𝐘 m
MGU t u n = Min (t ≈ u) n ∘ toSub

AMGU : (t u : Tm m) (σ : AList m n) → 𝐘 n
AMGU t u σ l = Min ((t ≈ u) [ toSub σ ⨟]) _ ∘ toSub

AMGUⁿ : (ts us : Tm m ^ k) (σ : AList m n) → 𝐘 n
AMGUⁿ ts us σ l = Min ((ts ≈ us) [ toSub σ ⨟]) _ ∘ toSub

DecMGU : (t u : Tm m) → Set
DecMGU t u = (∃₂ $ MGU t u) ⊎ (¬ₘ {_} {Sub} $ t ≈ u)

DecAMGU : (t u : Tm m) (σ : AList m n) → Set
DecAMGU t u σ = (∃₂ $ AMGU t u σ) ⊎ (¬ₘ {_} {Sub} $ t ≈ u [ toSub σ ⨟])

DecAMGUⁿ : (ts us : Tm m ^ k) (σ : AList m n) → Set
DecAMGUⁿ ts us σ = (∃₂ $ AMGUⁿ ts us σ) ⊎ (¬ₘ $ ts ≈ us [ toSub σ ⨟])

toSub-≗ : {P Q : 𝐘 m}
  → P ≗ Q
  → (λ n → P n ∘ toSub) ≗ λ n → Q n ∘ toSub
toSub-≗ P=Q ρ = record { to = P=Q (toSub ρ) .to ; from = P=Q (toSub ρ) .from}

t≈u⇔P : {P : 𝐘 m}
  → (t u : Tm m) (σ : AList m n)
  → (t ≈ u) ≗ P
  → AMGU t u σ ≗ (λ n → Min (P [ toSub σ ⨟]) n ∘ toSub)
t≈u⇔P t u σ = toSub-≗ ∘ Min≗ ∘ ext≗ (toSub σ) 

ts≈us⇔P : {P : 𝐘 m}
  → (t u : Tm m ^ k) (σ : AList m n)
  → (t ≈ u) ≗ P
  → AMGUⁿ t u σ ≗ (λ n → Min (P [ toSub σ ⨟]) n ∘ toSub)
ts≈us⇔P t u σ = toSub-≗ ∘ Min≗ ∘ ext≗ (toSub σ) 

-------------------------------------------------------------------------
-- Equivalences between most general unifiers
-------------------------------------------------------------------------

MGU=AMGU-id : (t u : Tm m) → MGU t u ≗ AMGU t u id
MGU=AMGU-id t u = toSub-≗ (Min≗ (P=Pid⨟- (t ≈ u)))

AMGU-sym
  : (u t : Tm m) (σ : AList m n)
  → AMGU t u σ ≗ AMGU u t σ
AMGU-sym u t σ = t≈u⇔P t u σ (≈-sym t u)

ts≈us=opᵢts≈opᵢus : {i : k ∈ D} (σ : Sub m n)
  → (ts ≈ us) _ σ ⇔ (op′ i ts ≈ op′ i us) _ σ
ts≈us=opᵢts≈opᵢus {i = i} σ = record { to = cong (op′ i) ; from = op-inj₃ }

AMGUⁿ=AMGU : {i : k ∈ D} (ts us : Tm m ^ k) (σ : AList m n)
  → AMGUⁿ ts us σ ≗ AMGU (op′ i ts) (op′ i us) σ
AMGUⁿ=AMGU ts us σ = ts≈us⇔P ts us σ ts≈us=opᵢts≈opᵢus

module _ (t u : Tm (suc m)) (x : Fin (suc m)) (r : Tm m) (σ : AList m n) where
  subst-equiv : (t ⟨ r for x ⟩ ≈ u ⟨ r for x ⟩ [ toSub σ ⨟]) ≗ (t ≈ u [ toSub (r / x ∷ σ) ⨟])
  subst-equiv ρ .to   eq = begin
    t ⟨ toSub (r / x ∷ σ) ⨟ ρ ⟩
      ≡⟨ t⟨fgh⟩=t⟨f⟩⟨gh⟩ t (r for x) _ _ ⟩
    t ⟨ r for x ⟩ ⟨ toSub σ ⨟ ρ ⟩
      ≡⟨ eq ⟩
    u ⟨ r for x ⟩ ⟨ toSub σ ⨟ ρ ⟩
      ≡⟨ sym (t⟨fgh⟩=t⟨f⟩⟨gh⟩ u (r for x) _ _) ⟩
    u ⟨ toSub (r / x ∷ σ) ⨟ ρ ⟩
      ∎

  subst-equiv ρ .from eq = begin
    t ⟨ r for x ⟩ ⟨ toSub σ ⨟ ρ ⟩
      ≡⟨ (sym $ t⟨fgh⟩=t⟨f⟩⟨gh⟩ t (r for x) _ _) ⟩
    t ⟨ r for x ⨟ toSub σ ⨟ ρ ⟩
      ≡⟨ eq ⟩
    u ⟨ r for x ⨟ toSub σ ⨟ ρ ⟩
      ≡⟨ t⟨fgh⟩=t⟨f⟩⟨gh⟩ u (r for x) _ _ ⟩
    u ⟨ r for x ⟩ ⟨ toSub σ ⨟ ρ ⟩
      ∎
  subst-equiv′ : AMGU (t ⟨ r for x ⟩) (u ⟨ r for x ⟩) σ ≗ AMGU t u (r / x ∷ σ)
  subst-equiv′ = toSub-≗ $ Min≗ subst-equiv

[]≈[] : (σ : AList m n) → AMGUⁿ [] [] σ _ []
[]≈[] σ = refl , λ where ρ refl → ρ , ⨟-idₗ ρ

module _(t u : Tm m) (ts us : Tm m ^ k) (σ : Sub m n) where 
  t∷ts≈u∷us⇔t≈u∧ts≈us : ((t ∷ ts) ≈ (u ∷ us)) _ σ ⇔ ((t ≈ u) ∧ (ts ≈ us)) _ σ
  t∷ts≈u∷us⇔t≈u∧ts≈us = record { to = V.∷-injective ; from = λ (t=u , ts=us) → cong₂ _∷_ t=u ts=us }

    
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
flex-mgu x (` y)     | yes (here refl) = inl (_ , id ,
  Min-id {ℕ} {Sub} (` y ≈ ` y) refl)
flex-mgu x (op′ _ _) | yes x∈ = inr λ where
  σ eq → op≢var (unify-occur σ x∈  eq)
... | no  x∉ = inl (_ , flexRigid∉ x∉ , Min-⨟-id _ _ (flexRigid∉-mgu x∉))

flex-amgu : (x : Fin m) (t : Tm m) → DecAMGU (` x) t id
flex-amgu x t with flex-mgu x t
... | inl (_ , ρ , x≈t) = inl (_ , ρ , MGU=AMGU-id (` x) t ρ .to x≈t)
... | inr x≉t = inr λ ρ eq → x≉t ρ (P=Pid⨟- ((` x) ≈ t) ρ .from eq)

----------------------------------------------------------------------
-- Correctness of amgu and amguⁿ
----------------------------------------------------------------------

mutual
  amgu⁺ : (t u : Tm m) (σ : AList m n) → DecAMGU t u σ

  amgu⁺ (op′ i ts) (op′ j us) σ with i ≟∈ j
  ... | no ¬p    = inr λ ρ eq → ¬p (op-inj₁₂ eq)
  ... | yes refl with amguⁿ⁺ ts us σ
  ... | inl (_ , ρ , Pρ) = inl (_ , ρ , AMGUⁿ=AMGU ts us σ ρ .to Pρ)
  ... | inr ts≉us        = inr λ ρ eq → ts≉us ρ (ts≈us=opᵢts≈opᵢus (toSub σ ⨟ ρ) .from eq)

  amgu⁺ (` x)      t     []          = flex-amgu x t
  amgu⁺ t          (` y) []          with flex-amgu y t
  ... | inl (_ , ρ , y≈t) = inl (_ , ρ , AMGU-sym t (` y) [] ρ .to y≈t)
  ... | inr y≉t           = inr (λ ρ eq → y≉t ρ (sym eq))

  amgu⁺ t          u     (r / x ∷ σ) with amgu⁺ (t ⟨ r for x ⟩) (u ⟨ r for x ⟩) σ
  ... | inl (_ , ρ , t≈u) = inl (_ , ρ , subst-equiv′ t u x r σ ρ .to t≈u)
  ... | inr t≉u           = inr λ ρ eq → t≉u ρ (subst-equiv t u x r σ ρ .from eq)

  amguⁿ⁺ : (ts us : Tm m ^ l) (σ : AList m n) → DecAMGUⁿ ts us σ
  amguⁿ⁺ []       []       σ = inl (_ , [] , []≈[] σ)
  amguⁿ⁺ (t ∷ ts) (u ∷ us) σ with amgu⁺ t u σ
  ... | inr t≉u = inr λ ρ eq → t≉u ρ (V.∷-injectiveˡ eq)
  ... | inl (_ , ρ , t≈u) with amguⁿ⁺ ts us (σ ⨟ ρ)
  ... | inr ts≉us           = inr λ γ ts≈us →
    failure-propagate {P = t ≈ u} {ts ≈ us} (toSub σ) (toSub ρ) t≈u (λ γ eq → ts≉us γ (begin
      ts ⟨ toSub (σ ⨟ ρ) ⨟ γ ⟩
        ≡⟨ cong (λ ρ → ts ⟨ ρ ⨟ γ ⟩) (toSub-++ σ ρ) ⟩
      ts ⟨ toSub σ ⨟ toSub ρ ⨟ γ ⟩
        ≡⟨ eq ⟩
      us ⟨ toSub σ ⨟ toSub ρ ⨟ γ ⟩
        ≡⟨ cong (λ ρ → us ⟨ ρ ⨟ γ ⟩) (sym (toSub-++ σ ρ)) ⟩
      us ⟨ toSub (σ ⨟ ρ) ⨟ γ ⟩
        ∎)) γ
      $ V.∷-injective ts≈us 
  ... | inl (_ , γ , ts≈us) = inl (_ , ρ ⨟ γ , ?)

mgu⁺ : (t u : Tm m) → DecMGU t u
mgu⁺ t u with amgu⁺ t u []
... | inl (_ , σ , t≈u) = inl $ _ , σ , MGU=AMGU-id t u σ .from t≈u
... | inr t≉u           = inr λ σ eq → t≉u σ ((P=Pid⨟- (t ≈ u)) σ .to eq)
