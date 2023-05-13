{-# OPTIONS --with-K  #-}

open import Prelude
  hiding (_++_; _+_)
open import Syntax.Simple.Description

module Syntax.Simple.Unification.Properties (D : Desc) where

open import Syntax.Simple.Term        D
open import Syntax.Simple.Association D
open import Syntax.Simple.Unification D
open import Syntax.Simple.Properties  D

open N using (_+_)

open ≡-Reasoning

private variable
  m n l i j k : ℕ
  t u     : Tm m
  ts us   : Tm m ^ k
  σ σ₁ σ₂ : Sub m n
  x y     : Fin m
  
module _ {Obj : Set} {Mor : Obj → Obj → Set} {F : Obj → Set}
  ⦃ _ : IsCategory Obj Mor ⦄ ⦃ _ : IsPresheaf F ⦄ where

  private variable
    a b c d e : Obj

  infix 6 _≈_
  
  t⟨fgh⟩=t⟨f⟩⟨gh⟩
    : (x : F a) (f : Mor a b) (g : Mor b c) (h : Mor c d)
    → x ⟨ f ⨟ g ⨟ h ⟩ ≡ x ⟨ f ⟩ ⟨ g ⨟ h ⟩
  t⟨fgh⟩=t⟨f⟩⟨gh⟩ x f g h = begin
    x ⟨ f ⨟ g ⨟ h ⟩
      ≡⟨ cong (x ⟨_⟩) (⨟-assoc f g h) ⟩
    x ⟨ f ⨟ (g ⨟ h) ⟩
      ≡⟨ ⟨⟩-⨟ f (g ⨟ h) x ⟩
    x ⟨ f ⟩ ⟨ g ⨟ h ⟩
      ∎

  _≈_
    : (x y : F a) → 𝐘 a
  (x ≈ y) _ f = x ⟨ f ⟩ ≡ y ⟨ f ⟩

  ≈-sym : (x y : F c) 
    → x ≈ y ≗ y ≈ x
  ≈-sym x y σ = record
    { to   = sym
    ; from = sym }
    where open Equivalence

{-
  unifies-⨟
    : (σ : Mor A B) (ρ : Mor B C)
    → (t u : Tm A)
    → t ≈ u $ σ
    → t ≈ u $ σ ⨟ ρ
  unifies-⨟ σ ρ t u eq = begin
    t ⟨ σ ⨟ ρ ⟩
      ≡⟨ ⟨⟩-⨟ _ _ t ⟩
    t ⟨ σ ⟩ ⟨ ρ ⟩
      ≡⟨ cong _⟨ ρ ⟩ eq ⟩
    u ⟨ σ ⟩ ⟨ ρ ⟩
      ≡⟨ sym $ ⟨⟩-⨟ _ _ u ⟩
    u ⟨ σ ⨟ ρ ⟩
      ∎
-}   

---------------------------------------------------------------------------
-- Variable Elimination Lemma

module Variable-Elimination {m : ℕ} (σ : Sub (suc m) n) (x : Fin (suc m)) (t : Tm m) where
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

module _ {m : ℕ} {x : Fin (suc m)} where
  ≈-flexRigid∉
    : {t : Tm (suc m)}
    → (x∉ : x ∉ₜ t)
    → (` x ≈ t) _ $ punchOutTm x∉ for x
  ≈-flexRigid∉ {t} x∉ = begin
    ` x ⟨ (punchOutTm x∉) for x ⟩
      ≡⟨ x⟨t/x⟩=t x ⟩
    punchOutTm x∉
      ≡⟨ sym (punchIn-t⟨u/x⟩=t (punchOutTm x∉)) ⟩
    punchInTm x (punchOutTm x∉) ⟨ (punchOutTm x∉) for x ⟩
      ≡⟨ (cong _⟨ punchOutTm x∉ for x ⟩ $ punchInTm-punchOutTm x∉) ⟩
    t ⟨ (punchOutTm x∉) for x ⟩
      ∎

  flexRigid∉-mgu
    : {t : Tm (suc m)}
    → (x∉ : x ∉ₜ t)
    → Min (` x ≈ t) _ (punchOutTm x∉ for x)
  flexRigid∉-mgu {t} x∉ = ≈-flexRigid∉ x∉ , λ σ eq →
    tabulate (lookup σ ∘ punchIn x) , (var-elim σ x _ (begin
      ` x ⟨ σ ⟩
        ≡⟨ eq  ⟩
      t ⟨ σ ⟩
        ≡⟨ (sym $ cong _⟨ σ ⟩ $ punchInTm-punchOutTm x∉) ⟩
      punchInTm x (punchOutTm x∉) ⟨ σ ⟩
        ∎))

-------------------------------------------------------------------------
-- Definition of Most General Unifier and its variant with an accumulator
-------------------------------------------------------------------------

MGU : (t u : Tm m) →  𝐘 m
MGU {m} t u n = Min (t ≈ u) n ∘ toSub

AMGU : (t u : Tm m) (σ : AList m n) → 𝐘 n
AMGU {m} {n} t u σ l = Min ((t ≈ u) [ toSub σ ⨟]) _ ∘ toSub

AMGUⁿ : (ts us : Tm m ^ k) (σ : AList m n) → 𝐘 n
AMGUⁿ {m} {k} {n} ts us σ l = Min ((ts ≈ us) [ toSub σ ⨟]) _ ∘ toSub

toSub-⇔ : {P Q : 𝐘 m}
  → P ≗ Q
  → (λ _ → P _ ∘ toSub) ≗ λ _ → Q _ ∘ toSub 
toSub-⇔ P=Q ρ = record { to = P=Q (toSub ρ) .to ; from = P=Q (toSub ρ) .from}
  where open Equivalence

AMGUⁿ=AMGU : {i : k ∈ D} (ts us : Tm m ^ k) (σ : AList m n)
  → AMGUⁿ ts us σ ≗ AMGU (op′ i ts) (op′ i us) σ
AMGUⁿ=AMGU {k} {m} {i = i} ts us σ = toSub-⇔ (Min≗ (ext≗ helper {toSub σ}))
  where
    helper : ∀ {n} (σ : Sub m n) → (ts ≈ us) _ σ ⇔ (op′ i ts ≈ op′ i us) _ σ  
    helper σ = record { to   = cong (op′ i) ; from = op-inj₃ }

MGU=AMGU-id : (t u : Tm m) → MGU t u ≗ AMGU t u id
MGU=AMGU-id t u {n} σ = toSub-⇔ (Min≗ (P=Pid⨟- (t ≈ u))) σ

∃MGU=∃AMGU-id : (t u : Tm m) → (∃₂ $ MGU t u) ⇔ (∃₂ $ AMGU t u [])
∃MGU=∃AMGU-id t u = ≗→⇔ (MGU=AMGU-id t u)

AMGU-sym
  : (u t : Tm m) (σ : AList m n)
  → AMGU t u σ ≗ AMGU u t σ
AMGU-sym u t σ = toSub-⇔ (Min≗ λ ρ → ≈-sym t u (toSub σ ⨟ ρ))

subst-equiv : (t u : Tm (suc m)) (x : Fin (suc m)) (r : Tm m) (σ : AList m n)
  → (∃₂ $ AMGU (t ⟨ r for x ⟩) (u ⟨ r for x ⟩) σ) ⇔ (∃₂ $ AMGU t u (r / x ∷ σ))
subst-equiv t u x r σ = ≗→⇔ (toSub-⇔ (Min≗ helper))
  where
    open Equivalence
    helper : (t ⟨ r for x ⟩ ≈ u ⟨ r for x ⟩ [ toSub σ ⨟])
      ≗ (t ≈ u [ toSub (r / x ∷ σ) ⨟])
    helper ρ .to   eq = begin
      t ⟨ toSub (r / x ∷ σ) ⨟ ρ ⟩
        ≡⟨ t⟨fgh⟩=t⟨f⟩⟨gh⟩ t (r for x) _ _ ⟩
      t ⟨ r for x ⟩ ⟨ toSub σ ⨟ ρ ⟩
        ≡⟨ eq ⟩
      u ⟨ r for x ⟩ ⟨ toSub σ ⨟ ρ ⟩
        ≡⟨ sym (t⟨fgh⟩=t⟨f⟩⟨gh⟩ u (r for x) _ _) ⟩
      u ⟨ toSub (r / x ∷ σ) ⨟ ρ ⟩
        ∎
    helper ρ .from eq = begin
      t ⟨ r for x ⟩ ⟨ toSub σ ⨟ ρ ⟩
        ≡⟨ (sym $ t⟨fgh⟩=t⟨f⟩⟨gh⟩ t (r for x) _ _) ⟩
      t ⟨ r for x ⨟ toSub σ ⨟ ρ ⟩
        ≡⟨ eq ⟩
      u ⟨ r for x ⨟ toSub σ ⨟ ρ ⟩
        ≡⟨ t⟨fgh⟩=t⟨f⟩⟨gh⟩ u (r for x) _ _ ⟩
      u ⟨ r for x ⟩ ⟨ toSub σ ⨟ ρ ⟩
        ∎
      
----------------------------------------------------------------------
-- Correctness of amgu
----------------------------------------------------------------------
flex-mgu′
  : (x : Fin m) (t : Tm m) → Dec (∃₂ $ MGU (` x) t)
flex-mgu′ {suc m} x t with x ∈ₜ? t
flex-mgu′ x (` y)     | yes (here refl) = yes (_ , id ,
  Min-id {ℕ} {Sub} (` y ≈ ` y) refl)
flex-mgu′ x (op′ _ _) | yes x∈ = no λ where
  (_ , σ , eq , min) → op≢var (unify-occur (toSub σ) x∈ eq)
... | no  x∉ = yes (_ , flexRigid∉ x∉ , Min-⨟-id {ℕ} {Sub} _ _ (flexRigid∉-mgu x∉))

flex-mgu
  : (x : Fin m) (t : Tm m) 
  → Dec (∃₂ $ AMGU (` x) t id)
flex-mgu x t = Dec⇔ (∃MGU=∃AMGU-id (` x) t) (flex-mgu′ x t)

mutual
  amgu⁺ : (t u : Tm m) (σ : AList m n) → Dec (∃₂ $ AMGU t u σ)

  amgu⁺ (op′ i ts) (op′ j us) σ with i ≟∈ j
  ... | no ¬p    = no λ where (_ , ρ , p , _) → ¬p (op-inj₁₂ p)
  ... | yes refl = Dec⇔ (≗→⇔ (AMGUⁿ=AMGU ts us σ)) $ amguⁿ⁺ ts us σ

  amgu⁺ (` x)      t     []          = flex-mgu x t
  amgu⁺ t          (` y) []          = Dec⇔
    (≗→⇔ (AMGU-sym t (` y) [])) $ flex-mgu y t

  amgu⁺ t          u     (r / x ∷ σ) =
    Dec⇔ (subst-equiv t u x r σ) (amgu⁺ (t ⟨ r for x ⟩) (u ⟨ r for x ⟩) σ)

  amguⁿ⁺ : (ts us : Tm m ^ l) (σ : AList m n) → Dec (∃₂ $ AMGUⁿ ts us σ)
  amguⁿ⁺ []       []       σ = yes (_ , [] , refl , λ ρ Pρ → ρ , ⨟-idₗ ρ)
  amguⁿ⁺ (t ∷ ts) (u ∷ us) σ with amgu⁺ t u σ
  ... | no ¬p = no {!!}
  ... | yes (_ , ρ , Pρ , min) with amguⁿ⁺ ts us (σ ⨟ ρ)
  ... | no ¬q = {!!}
  ... | yes p = {!!}

mgu⁺ : (t u : Tm m) → Dec (∃₂ $ MGU t u)
mgu⁺ t u = Dec⇔ (⇔-sym $ ∃MGU=∃AMGU-id t u) (amgu⁺ t u [])
