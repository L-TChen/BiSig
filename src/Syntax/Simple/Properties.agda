{-# OPTIONS --with-K --safe #-}

open import Prelude
  hiding (_++_; _+_)
open import Syntax.Simple.Description

module Syntax.Simple.Properties (D : Desc) where

open import Syntax.Simple.Term        D

open N using (_+_)

open ≡-Reasoning

private variable
  Γ Δ Ξ Θ m n l i j k : ℕ
  ts us   : Tm Ξ ^ n
  σ₁ σ₂   : Sub Γ Δ
  x y     : Fin Ξ
  t u v   : Tm Ξ

------------------------------------------------------------------------------
-- Trivial proofs

var≢op : {x : Fin m} {i : D .Op} {ts : Tm m ^ D .rules i}
  → op (i , ts) ≢ ` x
var≢op ()

op≢var : {x : Fin m} {i : D .Op} {ts : Tm m ^ D .rules i}
  → ` x ≢ op (i , ts)
op≢var()

op-inj
  : {(i , ts) (j , us) : ⟦ D ⟧ (Tm Ξ)}
  → _≡_ {A = Tm _ } (op (i , ts)) (op (j , us))
  → Σ (i ≡ j) λ where refl → ts ≡ us
  -- Σ (l ≡ k) λ where refl → Σ (i ≡ j) λ where refl → ts ≡ us
op-inj refl = refl , refl

op-inj₁₂
  : {(i , ts) (j , us) : ⟦ D ⟧ (Tm Ξ)}
  → _≡_ {A = Tm _ } (op (i , ts)) (op (j , us))
  → i ≡ j -- (l , i) ≡ (k , j)
op-inj₁₂ refl = refl

op-inj₃
  : {i : D .Op} {ts us : Tm Ξ ^ D .rules i}
  → op′ i ts ≡ op′ i us
  → ts ≡ us
op-inj₃ refl = refl

op-cong⇔ : {i : D .Op} 
  → {ts us : Vec (Tm Θ) (D .rules i)}
  → ts ≡ us ⇔ op (i , ts) ≡ op (i , us)
op-cong⇔ = record { to = cong (op′ _) ; from = op-inj₃ }

------------------------------------------------------------------------------
-- Proofs about free variables
{-
mutual
  ∈ₜ→∈fv : x ∈ᵥ t → x ∈ fv t
  ∈ₜ→∈fv (here p) = here p
  ∈ₜ→∈fv (op   p) = ∈ₜ→∈fvⁿ p

  ∈ₜ→∈fvⁿ : x ∈ᵥₛ ts → x ∈ fvⁿ ts
  ∈ₜ→∈fvⁿ (head x∈)         = ∈-++⁺ˡ        (∈ₜ→∈fv x∈)
  ∈ₜ→∈fvⁿ (tail {_} {t} x∈) = ∈-++⁺ʳ (fv t) (∈ₜ→∈fvⁿ x∈)

module _ {m : ℕ} where mutual 
  ∈fv→∈ₜ : {t : Tm m} {x : Fin m} → x ∈ fv t → x ∈ᵥ t
  ∈fv→∈ₜ {` x}  (here px) = here px
  ∈fv→∈ₜ {op _} x∈        = op (∈fv→∈ₜⁿ x∈)

  ∈fv→∈ₜⁿ : {x : Fin m} {ts : Tm m ^ l} → x ∈ fvⁿ ts → x ∈ᵥₛ ts
  ∈fv→∈ₜⁿ  {suc l} {x} {ts = t ∷ ts} x∈ with ∈-++⁻ (fv t) x∈
  ... | inl x∈t  = head (∈fv→∈ₜ x∈t)
  ... | inr x∈ts = tail (∈fv→∈ₜⁿ x∈ts)
-}
∈→≡ : x ∈ᵥ ` y → x ≡ y
∈→≡  (here x=y) = x=y

module _ {σ₁ σ₂ : Sub Γ Δ} where mutual
  ≡-fv-inv : (A : Tm Γ) 
    → A ⟨ σ₁ ⟩ ≡ A ⟨ σ₂ ⟩
    → x ∈ᵥ A
    → lookup σ₁ x ≡ lookup σ₂ x
  ≡-fv-inv (` x)      p (here refl) = p
  ≡-fv-inv (op′ i ts) p (op x∈)    = ≡-fv-invⁿ ts (op-inj₃ p) x∈

  ≡-fv-invⁿ : (As : Tm Γ ^ n)
    → subⁿ σ₁ As ≡ subⁿ σ₂ As
    → x ∈ᵥₛ As
    → lookup σ₁ x ≡ lookup σ₂ x
  ≡-fv-invⁿ (A ∷ As) p (head x∈) = ≡-fv-inv  A  (V.∷-injectiveˡ p) x∈
  ≡-fv-invⁿ (A ∷ As) p (tail x∈) = ≡-fv-invⁿ As (V.∷-injectiveʳ p) x∈

module _ {σ₁ σ₂ : Sub Γ Δ} where mutual
  ≡-fv : (A : Tm Γ)
    → (∀ {x} → x ∈ᵥ A → lookup σ₁ x ≡ lookup σ₂ x)
    → A ⟨ σ₁ ⟩ ≡ A ⟨ σ₂ ⟩
  ≡-fv (` x)      p = p (here refl)
  ≡-fv (op′ _ ts) p = cong (λ ts → op′ _ ts) (≡-fvⁿ ts (p ∘ op)) -- (≡-fvⁿ ts p)

  ≡-fvⁿ : {n : ℕ} (As : Tm Γ ^ n)
    → (∀ {x} → x ∈ᵥₛ As → lookup σ₁ x ≡ lookup σ₂ x)
    → subⁿ σ₁ As ≡ subⁿ σ₂ As
  ≡-fvⁿ {zero}  []       _ = refl
  ≡-fvⁿ {suc n} (A ∷ As) p = cong₂ _∷_
    (≡-fv A (p ∘ head)) (≡-fvⁿ As (p ∘ tail))

------------------------------------------------------------------------------
-- Renames are also substitutions

module _ {ρ : Fin m → Fin n} where mutual
  rename-is-sub
    : (t : Tm m)
    → t ⟨ tabulate (`_ ∘ ρ) ⟩ ≡ t ⟨ ρ ⟩
  rename-is-sub (` x)      = lookup∘tabulate _ x
  {- begin
    lookup (tabulate (`_ ∘ ρ)) x
      ≡⟨ lookup∘tabulate (`_ ∘ ρ) x ⟩
    ` ρ x
      ≡⟨ cong `_ (sym $ lookup∘tabulate ρ x) ⟩
    ` lookup (tabulate ρ) x
      ∎
   -}
  rename-is-sub (op′ i ts) = cong (op′ i) (rename-is-subⁿ ts)

  rename-is-subⁿ
    : (ts : Tm m ^ k)
    → ts ⟨ tabulate (`_ ∘ ρ) ⟩ ≡ ts ⟨ ρ ⟩
  rename-is-subⁿ []       = refl
  rename-is-subⁿ (t ∷ ts) = cong₂ _∷_ (rename-is-sub t) (rename-is-subⁿ ts)
