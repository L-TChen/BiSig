{-# OPTIONS --with-K --safe #-}

open import Prelude
  hiding (_++_; _+_)
open import Syntax.Simple.Description

module Syntax.Simple.Properties (D : Desc) where

open import Syntax.Simple.Term        D

open N using (_+_)

open ≡-Reasoning

private variable
  Γ Δ Ξ m n l i j k : ℕ
  ts us   : Tm Ξ ^ n
  σ₁ σ₂   : Sub Γ Δ
  x y     : Fin Ξ

private variable
  t u v : Tm m

------------------------------------------------------------------------------
-- Trivial proofs

var≢op : (x : Fin m) (i : l ∈ D) (ts : Tm m ^ l)
  → op (_ , i , ts) ≢ ` x
var≢op _ _ _ ()

op-inj
  : {(l , i , ts) (k , j , us) : ⟦ D ⟧ (Tm Ξ)}
  → op (l , i , ts) ≡ op (k , j , us)
  → Σ (l ≡ k) λ where refl → Σ (i ≡ j) λ where refl → ts ≡ us
op-inj refl = refl , refl , refl

op-inj₁₂
  : {(l , i , ts) (k , j , us) : ⟦ D ⟧ (Tm Ξ)}
  → op (l , i , ts) ≡ op (k , j , us)
  → (l , i) ≡ (k , j)
op-inj₁₂ refl = refl

op-inj₃
  : {i : n ∈ D} {ts us : Tm Ξ ^ n}
  → op′ i ts ≡ op′ i us
  → ts ≡ us
op-inj₃ refl = refl

------------------------------------------------------------------------------
-- Proofs about free variables

mutual
  ∈ₜ→∈fv : {x : Fin m} {t : Tm m} → x ∈ₜ t → x ∈ fv t
  ∈ₜ→∈fv (here p) = here p
  ∈ₜ→∈fv (ops p)  = ∈ₜ→∈fvⁿ p

  ∈ₜ→∈fvⁿ : {x : Fin m} {ts : Tm m ^ l} → x ∈ₜₛ ts → x ∈ fvⁿ ts
  ∈ₜ→∈fvⁿ (head x∈)         = ∈-++⁺ˡ        (∈ₜ→∈fv x∈)
  ∈ₜ→∈fvⁿ (tail {_} {t} x∈) = ∈-++⁺ʳ (fv t) (∈ₜ→∈fvⁿ x∈)

module _ {m : ℕ} where mutual 
  ∈fv→∈ₜ : {t : Tm m} {x : Fin m} → x ∈ fv t → x ∈ₜ t
  ∈fv→∈ₜ {` x}  (here px) = here px
  ∈fv→∈ₜ {op _} x∈        = ops $ ∈fv→∈ₜⁿ x∈

  ∈fv→∈ₜⁿ : {x : Fin m} {ts : Tm m ^ l} → x ∈ fvⁿ ts → x ∈ₜₛ ts
  ∈fv→∈ₜⁿ  {suc l} {x} {ts = t ∷ ts} x∈ with ∈-++⁻ (fv t) x∈
  ... | inl x∈t  = head (∈fv→∈ₜ x∈t)
  ... | inr x∈ts = tail (∈fv→∈ₜⁿ x∈ts)

module _ {σ₁ σ₂ : Sub Γ Δ} where mutual
  ≡-fv-inv : (A : Tm Γ) 
    → A ⟨ σ₁ ⟩ ≡ A ⟨ σ₂ ⟩
    → x ∈ fv A
    → lookup σ₁ x ≡ lookup σ₂ x
  ≡-fv-inv (` x)      p (here refl) = p
  ≡-fv-inv (op′ i ts) p j = ≡-fv-invⁿ ts (op-inj₃ p) j

  ≡-fv-invⁿ : {n : ℕ} (As : Tm Γ ^ n)
    → subⁿ σ₁ As ≡ subⁿ σ₂ As
    → x ∈ fvⁿ As
    → lookup σ₁ x ≡ lookup σ₂ x
  ≡-fv-invⁿ {n = suc n} (A ∷ As) p i with ∈-++⁻ (fv A) i
  ... | inl j = ≡-fv-inv  A  (V.∷-injectiveˡ p) j
  ... | inr j = ≡-fv-invⁿ As (V.∷-injectiveʳ p) j

module _ (σ₁ σ₂ : Sub Γ Δ) where mutual
  ≡-fv : (A : Tm Γ)
    → (∀ {x} → x ∈ fv A → lookup σ₁ x ≡ lookup σ₂ x)
    → A ⟨ σ₁ ⟩ ≡ A ⟨ σ₂ ⟩
  ≡-fv (` x)      p = p (here refl)
  ≡-fv (op′ _ ts) p = cong (λ ts → op′ _ ts) (≡-fvⁿ ts p)

  ≡-fvⁿ : {n : ℕ} (As : Tm Γ ^ n)
    → (∀ {x} → x ∈ fvⁿ  As → lookup σ₁ x ≡ lookup σ₂ x)
    → subⁿ σ₁ As ≡ subⁿ σ₂ As
  ≡-fvⁿ {zero}  []       _ = refl
  ≡-fvⁿ {suc n} (A ∷ As) p = cong₂ _∷_
    (≡-fv A λ k → p (∈-++⁺ˡ k)) (≡-fvⁿ As λ k → p (∈-++⁺ʳ (fv A) k))

{-
SubFv : List (Fin Ξ) → ℕ → Set
SubFv xs Δ = Σ[ ys ∈ List (Fin _ × Tm Δ) ] map proj₁ ys ≡ xs

Covered : {Ξ : ℕ} → List (Fin Ξ) → Set
Covered xs = (x : Fin _) → x ∈ xs
-}

------------------------------------------------------------------------------
-- t ≺ (p ▷ t)
------------------------------------------------------------------------------
size-ʳ++
  : (ys : Tm m ^ j) (xs : Tm m ^ i)
  → sizeⁿ (ys ʳ++ xs) ≡ sizeⁿ ys + sizeⁿ xs
size-ʳ++ []       xs = refl
size-ʳ++ (x ∷ ys) xs with size-ʳ++ ys (x ∷ xs)
... | p = begin
  sizeⁿ (ys ʳ++ (x ∷ xs))
    ≡⟨ p ⟩
  sizeⁿ ys + (size x + sizeⁿ xs)
    ≡⟨ (sym $ +-assoc (sizeⁿ ys) _ _) ⟩
  (sizeⁿ ys + size x) + sizeⁿ xs
    ≡⟨ cong (_+ sizeⁿ xs) (+-comm (sizeⁿ ys) (size x))  ⟩
  size x + sizeⁿ ys + sizeⁿ xs
    ∎

ʳ++-size
  : (k : j ʳ+ (suc i) ∈ D) (ys : Tm m ^ j) (x : Tm m) (xs : Tm m ^ i)
  → size x < size (op′ k (ys ʳ++ (x ∷ xs)))
ʳ++-size {j} {i} {m} k ys x xs = less-than-or-equal $ cong suc $ begin
  size x + (sizeⁿ xs + sizeⁿ ys)
    ≡⟨ (sym $ +-assoc (size x) _ _) ⟩
  (size x + sizeⁿ xs) + sizeⁿ ys
    ≡⟨ +-comm (size x + sizeⁿ xs) _ ⟩
  sizeⁿ ys + (size x + sizeⁿ xs)
    ≡⟨ (sym $ size-ʳ++ ys (x ∷ xs)) ⟩
  sizeⁿ (ys ʳ++ (x ∷ xs))
    ∎
 
▷₁-size : (t : Tm m) (p : Step m)
  → t ≺ (p ▷₁ t)
▷₁-size t (step i ys xs) = ʳ++-size i ys t xs 

------------------------------------------------------------------------------
-- Substitution, unification relation between substitutions

module _ {Obj : Set} {Mor : Obj → Obj → Set} {Tm : Obj → Set}
  ⦃ _ : IsCategory Obj Mor ⦄ ⦃ _ : IsPresheaf Tm ⦄ where
  infix 4 _≈_by_

  private variable
    A B C : Obj

  _≈_by_
    : (t u : Tm A) → 𝐘 A
  t ≈ u by σ = t ⟨ σ ⟩ ≡ u ⟨ σ ⟩

  Unifies-sym
    : (t u : Tm A) (σ : Mor A B)
    → t ≈ u by σ → u ≈ t by σ
  Unifies-sym t u σ eq = sym eq

  unifies-⨟
    : (σ : Mor A B) (ρ : Mor B C)
    → (t u : Tm A)
    → t ≈ u by σ
    → t ≈ u by σ ⨟ ρ
  unifies-⨟ σ ρ t u eq = begin
    t ⟨ σ ⨟ ρ ⟩
      ≡⟨ ⟨⟩-⨟ _ _ t ⟩
    t ⟨ σ ⟩ ⟨ ρ ⟩
      ≡⟨ cong _⟨ ρ ⟩ eq ⟩
    u ⟨ σ ⟩ ⟨ ρ ⟩
      ≡⟨ sym $ ⟨⟩-⨟ _ _ u ⟩
    u ⟨ σ ⨟ ρ ⟩
      ∎

  id-minimal
    : (σ : Mor A B)
    → (t : Tm A)
    → Min {Obj} (λ ρ → t ≈ t by σ ⨟ ρ) id
  id-minimal σ t = refl , λ g eq → g , (begin
    g
      ≡⟨ sym (⨟-idₗ g) ⟩
    id ⨟ g
      ∎)

------------------------------------------------------------------------------
-- Proofs about ⟪ t for x ⟫

sub-t-for-x-x
  : {t : Tm m} {x : Fin (suc m)}
  → sub-for t x x ≡ t
sub-t-for-x-x {x = x} with x ≟ x
... | yes p = refl
... | no ¬p = ⊥-elim₀ (¬p refl)

sub-t-for-x-y
  : {x y : Fin (suc m)} {t : Tm m} 
  → (¬p : x ≢ y)
  → sub-for t x y ≡ ` punchOut ¬p 
sub-t-for-x-y {x = x} {y} ¬p with x ≟ y
... | yes p = ⊥-elim₀ (¬p p)
... | no ¬p = refl

sub-for-x-in-x : {t : Tm m} (x : Fin (suc m))
  → ` x ⟨ t for x ⟩ ≡ t
sub-for-x-in-x {t = t} x = begin
  ` x ⟨ t for x ⟩
    ≡⟨ lookup∘tabulate (sub-for t x) x ⟩
  sub-for t x x
    ≡⟨ sub-t-for-x-x ⟩
  t
    ∎

sub-for-x-in-y : {t : Tm m} {x y : Fin (suc m)}
  → (¬p : x ≢ y)
  → ` y ⟨ t for x ⟩ ≡ ` punchOut ¬p
sub-for-x-in-y {m} {t} {x} {y} ¬p = begin
  ` y ⟨ t for x ⟩
    ≡⟨ lookup∘tabulate (sub-for t x) y ⟩
  sub-for t x y
    ≡⟨ sub-t-for-x-y ¬p ⟩
  ` F.punchOut ¬p
    ∎

module _ {u : Tm m} {x : Fin (suc m)} where mutual
  sub-for-nonfree=punchOut : (t : Tm (suc m)) (x∉ : x ∉ₜ t)
    → t ⟨ u for x ⟩ ≡ punchOutTm x∉
  sub-for-nonfree=punchOut (` y)  x∉ with x ≟ y
  ... | yes p = ⊥-elim₀ (x∉ (here p))
  ... | no ¬p = sub-for-x-in-y ¬p
  sub-for-nonfree=punchOut (op (_ , i , ts)) x∉ =
    cong (λ ts → op′ i ts) (sub-for-nonfree=punchOutⁿ ts (x∉ ∘ ops))

  sub-for-nonfree=punchOutⁿ : (ts : Tm (suc m) ^ n)
    → (x∉ : x ∉ₜₛ ts)
    → subⁿ (u for x) ts ≡ punchOutTmⁿ x∉
  sub-for-nonfree=punchOutⁿ []       _  = refl
  sub-for-nonfree=punchOutⁿ (t ∷ ts) x∉ =
    cong₂ _∷_ (sub-for-nonfree=punchOut t $ x∉ ∘ head)
      (sub-for-nonfree=punchOutⁿ ts (x∉ ∘ tail))

punchOut-for-x≢y
  : {x y : Fin (suc m)}
  → (¬p : x ≢ y)
  → ` x ⟨ (` punchOut ¬p) for x ⟩ ≡ ` y ⟨ (` punchOut ¬p) for x ⟩
punchOut-for-x≢y {x = x} {y} ¬p = begin
  ` x ⟨ (` punchOut ¬p) for x ⟩
    ≡⟨ sub-for-x-in-x x ⟩
  ` punchOut ¬p
    ≡⟨ (sym $ sub-for-x-in-y ¬p) ⟩
  ` y ⟨ (` punchOut ¬p) for x ⟩
    ∎

------------------------------------------------------------------------------
-- Occurrence check

++-▷ : (ps qs : Steps n) (t : Tm n)
  → ps L.++ qs ▷ t ≡ ps ▷ qs ▷ t
++-▷ []                 qs t = refl
++-▷ (step i us ts ∷ ps) qs t = 
  cong (λ u → op $ _ , i , us ʳ++ (u ∷ ts)) (++-▷ ps qs t) 

++-▷▷₁ : (ps : Steps n) (p : Step n) (t : Tm n)
  → ps ▷ (p ▷₁ t) ≡ ps L.++ L.[ p ] ▷ t
++-▷▷₁ []       p₀ t = refl
++-▷▷₁ (p ∷ ps) p₀ t = cong (p ▷₁_) (++-▷▷₁ ps p₀ t)

module _ {m : ℕ} {x : Fin m} where mutual
  ▷walk=id : {t : Tm m} → (x∈ : x ∈ₜ t)
    → t ≡ walk x∈ ▷ ` x
  ▷walk=id (here refl)              = refl
  ▷walk=id (ops {_} {i} {t ∷ _} x∈) = ▷walks=id i t [] x∈ 

  ▷walks=id : (i : l ʳ+ (suc k) ∈ D)
    → (t : Tm m) (us : Tm m ^ l) {ts : Tm m ^ k}
    → (x∈ : x ∈ₜₛ t ∷ ts)
    → op′ i (us ʳ++ (t ∷ ts)) ≡ walkTms i t us ts x∈ ▷ ` x
  ▷walks=id {l} {k} i t us (head x∈) =
    cong (λ t → op′ _ (us ʳ++ (t ∷ _))) (▷walk=id x∈)
  ▷walks=id i t₀ us {t ∷ _} (tail x∈) = ▷walks=id i t (t₀ ∷ us) x∈

sub-ʳ++
  : {σ : Sub m n}
  → (ts : Tm m ^ i) (us : Tm m ^ j)
  → (ts ʳ++ us) ⟨ σ ⟩ ≡ ts ⟨ σ ⟩ ʳ++ us ⟨ σ ⟩
sub-ʳ++ []       us = refl
sub-ʳ++ (x ∷ ts) us = sub-ʳ++ ts (x ∷ us)

sub-▷
  : {σ : Sub m n} (ps : Steps m) (t : Tm m)
  → (ps ▷ t) ⟨ σ ⟩ ≡ ps ⟨ σ ⟩ ▷ t ⟨ σ ⟩
sub-▷ []                          t = refl
sub-▷ {σ = σ} (step _ us ts ∷ ps) t =
  cong (λ ts → op′ _ ts) $ begin
    subⁿ σ (us ʳ++ ((ps ▷ t) ∷ ts))
      ≡⟨ sub-ʳ++ us _ ⟩
    subⁿ σ us ʳ++ (subⁿ σ ((ps ▷ t) ∷ ts))
      ≡⟨ cong (λ t → subⁿ σ us ʳ++ (t ∷ subⁿ σ ts)) (sub-▷ ps t) ⟩
    subⁿ σ us ʳ++ ((ps ⟨ σ ⟩ ▷ t ⟨ σ ⟩) ∷ subⁿ σ ts)
      ∎

------------------------------------------------------------------------------
-- 
------------------------------------------------------------------------------

sub-ps=[] : {σ : Sub m n} {ps : Steps m} → ps ⟨ σ ⟩ ≡ [] → ps ≡ []
sub-ps=[] { ps = [] } _ = refl

------------------------------------------------------------------------------
-- No Cycle Lemma
------------------------------------------------------------------------------

no-cycle′
  : (t : Tm m) (ps : Steps m) (@0 ac : Acc _≺_ t)
  → t ≡ ps ▷ t 
  → ps ≡ []
no-cycle′ _                   []                      _       _ = refl
no-cycle′ (op (l , pos , vs)) (step {j} k us ts ∷ ps) (acc g) p with op-inj p
... | refl , refl , eq with splitAt j vs
... | ys , x ∷ zs , refl with ▷₁-size x (step k ys zs)
... | x< = ⊥-elim₀ $ [xs]≢[] _ $ no-cycle′ x (ps L.++ _) (g x x<) $ begin
      x
        ≡⟨ V.∷-injectiveˡ $ ʳ++-≡ ys us eq .proj₂ ⟩
      ps ▷ step k ys zs ▷₁ x
        ≡⟨ ++-▷▷₁ ps (step k ys zs) x ⟩
      ps L.++ L.[ step k ys zs ] ▷ x
      ∎

no-cycle
  : (t : Tm m) (ps : Steps m)
  → t ≡ ps ▷ t 
  → ps ≡ []
no-cycle t ps = no-cycle′ t ps (≺-wf t)

unify-occurrence
  : (σ : Sub m n) {x : Fin m} {t : Tm m}
  → x ∈ₜ t
  → ` x ≈ t by σ
  → t ≡ ` x
unify-occurrence σ {x} {t} x∈ eq =
  let ps    = walk x∈
      ps=[] = sub-ps=[] $ no-cycle (t ⟨ σ ⟩) (ps ⟨ σ ⟩) $ begin
        t ⟨ σ ⟩
          ≡⟨ cong _⟨ σ ⟩ (▷walk=id x∈) ⟩
        (ps ▷ ` x) ⟨ σ ⟩
          ≡⟨ sub-▷ ps (` x) ⟩
        ps ⟨ σ ⟩ ▷ ` x ⟨ σ ⟩
          ≡⟨ cong ((ps ⟨ σ ⟩) ▷_) eq ⟩
        ps ⟨ σ ⟩ ▷ t ⟨ σ ⟩
          ∎
  in begin
    t
      ≡⟨ ▷walk=id x∈ ⟩
    ps ▷ ` x
      ≡⟨ cong (_▷ ` x) ps=[] ⟩
    [] ▷ ` x
      ≡⟨⟩
    ` x
    ∎ 
