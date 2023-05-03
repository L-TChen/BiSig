{-# OPTIONS --with-K  #-}

open import Prelude
  hiding (_++_; _+_)
open import Syntax.Simple.Description

module Syntax.Simple.Properties (D : Desc) where

open import Syntax.Simple.Term        D
open import Syntax.Simple.Association D
open import Syntax.Simple.Unification D

open N using (_+_)

open ≡-Reasoning

private variable
  Γ Δ Ξ m n l i j k : ℕ
  ts us   : Tm Ξ ^ n
  σ₁ σ₂   : Sub Γ Δ
  x y     : Fin Ξ

------------------------------------------------------------------------------
-- Order relation between substitutions

private variable
  t u v : Tm m

_⊑_ : Sub m n → Sub m l → Set
ρ ⊑ σ = ∃[ ρ′ ] ρ ≡ (σ ⨟ ρ′) 

Subₚ   = λ m → {n : ℕ} → Sub   m n → Set
AListₚ = λ m → {n : ℕ} → AList m n → Set

Unifies : (t u : Tm m) → Subₚ m
Unifies t u σ = t ⟪ σ ⟫ ≡ u ⟪ σ ⟫ 

Unifiesₐ : (t u : Tm m) → AListₚ m
Unifiesₐ t u σ = Unifies t u (toSub σ)

infixl 10 _[_⨟_]
_[_⨟_] : (P : Subₚ m) (σ : Sub m n) → Subₚ n
P [ σ ⨟ ρ ] = P (σ ⨟ ρ)

Max : Subₚ m → Subₚ m
Max P σ = P σ ×
  ({n : ℕ} (σ′ : Sub _ n) → P σ′ → σ′ ⊑  σ)
  
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

ʳ++-≡ : {A : Set}
  → (xs xs′ : Vec A n) {ys ys′ : Vec A m}
  → xs ʳ++ ys ≡ xs′ ʳ++ ys′
  → xs ≡ xs′ × ys ≡ ys′
ʳ++-≡ []       []         {ys} {ys′} p = refl , p
ʳ++-≡ (x ∷ xs) (x′ ∷ xs′) {ys} {ys′} eq with ʳ++-≡ xs xs′ {x ∷ ys} {x′ ∷ ys′} eq
... | refl , refl = refl , refl 

[xs]≢[] : {A : Set}
  → (xs : List A) {x : A}
  → xs L.++ L.[ x ] ≢ []
[xs]≢[] []       ()
[xs]≢[] (x ∷ xs) ()

------------------------------------------------------------------------------
-- Substitution has an identity and is associative 

module _ {m : ℕ} where mutual
  sub-id : (t : Tm m)
    → t ⟪ ids ⟫ ≡ t
  sub-id (` x)      = lookup∘tabulate `_ x
  sub-id (op′ i ts) = cong (λ ts → op′ i ts) (sub-idⁿ ts)

  sub-idⁿ : (t : Tm m ^ l)
    → subⁿ ids t ≡ t
  sub-idⁿ []       = refl
  sub-idⁿ (t ∷ ts) =
    cong₂ _∷_ (sub-id t) (sub-idⁿ ts)

module _ {m n l : ℕ} (ρ : Sub m n) (σ : Sub n l) where mutual
  sub-assoc : (t : Tm m)
    → t ⟪ ρ ⨟ σ ⟫ ≡ t ⟪ ρ ⟫ ⟪ σ ⟫
  sub-assoc (` x)      = lookup∘tabulate (λ i → lookup ρ i ⟪ σ ⟫) x
  sub-assoc (op′ i ts) = cong (λ ts → op′ i ts) (sub-assocⁿ ts)

  sub-assocⁿ : (ts : Tm m ^ k)
    → subⁿ (ρ ⨟ σ) ts ≡ subⁿ σ (subⁿ ρ ts) 
  sub-assocⁿ {zero}  []       = refl
  sub-assocⁿ {suc k} (t ∷ ts) = cong₂ _∷_ (sub-assoc t) (sub-assocⁿ ts)


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
  → ` x ⟪ t for x ⟫ ≡ t
sub-for-x-in-x {t = t} x = begin
  ` x ⟪ t for x ⟫
    ≡⟨ lookup∘tabulate (sub-for t x) x ⟩
  sub-for t x x
    ≡⟨ sub-t-for-x-x ⟩
  t
    ∎

sub-for-x-in-y : {t : Tm m} {x y : Fin (suc m)}
  → (¬p : x ≢ y)
  → ` y ⟪ t for x ⟫ ≡ ` punchOut ¬p
sub-for-x-in-y {m} {t} {x} {y} ¬p = begin
  ` y ⟪ t for x ⟫
    ≡⟨ lookup∘tabulate (sub-for t x) y ⟩
  sub-for t x y
    ≡⟨ sub-t-for-x-y ¬p ⟩
  ` F.punchOut ¬p
    ∎
  
module _ {u : Tm m} {x : Fin (suc m)} where mutual
  sub-for-nonfree=punchOut : (t : Tm (suc m)) (x∉ : x ∉ₜ t)
    → t ⟪ u for x ⟫ ≡ punchOutTm x∉
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
  → ` x ⟪ (` punchOut ¬p) for x ⟫ ≡ ` y ⟪ (` punchOut ¬p) for x ⟫
punchOut-for-x≢y {x = x} {y} ¬p = begin
  ` x ⟪ (` punchOut ¬p) for x ⟫
    ≡⟨ sub-for-x-in-x x ⟩
  ` punchOut ¬p
    ≡⟨ (sym $ sub-for-x-in-y ¬p) ⟩
  ` y ⟪ (` punchOut ¬p) for x ⟫
    ∎

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
    → A ⟪ σ₁ ⟫ ≡ A ⟪ σ₂ ⟫
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
    → A ⟪ σ₁ ⟫ ≡ A ⟪ σ₂ ⟫
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
-- Association list implies the inequality relation

AList→≥ : AList m n → n ≤ m
AList→≥ []           = ≤-refl
AList→≥ (t / x ∷ ge) = ≤-step (AList→≥ ge)

------------------------------------------------------------------------------
-- Proofs about toSub

toSub-∷
  : {u : Tm m} (x : Fin (suc m)) (ρ : AList m n)
  → (t : Tm (suc m))
  → t ⟪ u / x ∷ ρ ⟫ₐ ≡ t ⟪ u for x ⟫ ⟪ ρ ⟫ₐ
toSub-∷ {_} {_} {u} x ρ t = sub-assoc (u for x) (toSub ρ) t

toSub-∷[]
  : {u : Tm m} (x : Fin (suc m))
  → (t : Tm (suc m))
  → t ⟪ u / x ∷ [] ⟫ₐ ≡ t ⟪ u for x ⟫
toSub-∷[] {_} {u} x t = begin
  t ⟪ u / x ∷ [] ⟫ₐ
    ≡⟨ toSub-∷ x [] t ⟩
  t ⟪ u for x ⟫ ⟪ [] ⟫ₐ
    ≡⟨ sub-id _ ⟩
  t ⟪ u for x ⟫ 
    ∎

toSub-++
  : (ρ : AList m n) (σ : AList n l) 
  → (t : Tm m)
  → t ⟪ ρ ++ σ ⟫ₐ ≡ t ⟪ ρ ⟫ₐ ⟪ σ ⟫ₐ
toSub-++ []          σ t = cong _⟪ σ ⟫ₐ (sym $ sub-id t)
toSub-++ (u / x ∷ ρ) σ t = begin
  t ⟪ (u for x) ⨟ toSub (ρ ++ σ) ⟫
    ≡⟨ toSub-∷ x (ρ ++ σ) t ⟩
  t ⟪ u for x ⟫ ⟪ ρ ++ σ ⟫ₐ
    ≡⟨ toSub-++ ρ σ (t ⟪ u for x ⟫) ⟩
  t ⟪ u for x ⟫ ⟪ ρ ⟫ₐ ⟪ σ ⟫ₐ
    ≡⟨ cong (_⟪ σ ⟫ₐ) (sym $ toSub-∷ x ρ t) ⟩
  t ⟪ toSub (u / x ∷ ρ ) ⟫ ⟪ σ ⟫ₐ
    ∎

------------------------------------------------------------------------------
-- Proofs that amgu does provide a maximal general unifier

flexFlex≢-Unifies
  : {x y : Fin (suc m)}
  → (¬p : x ≢ y)
  → Unifiesₐ (` x) (` y) (flexFlex-≢ ¬p)
flexFlex≢-Unifies {_} {x} {y} ¬p = begin
  ` x ⟪ flexFlex-≢ ¬p ⟫ₐ
    ≡⟨ toSub-∷[] x (` x) ⟩
  ` x ⟪ (` punchOut ¬p) for x ⟫
    ≡⟨ punchOut-for-x≢y ¬p ⟩
  ` y ⟪ (` punchOut ¬p) for x ⟫
    ≡⟨ sym $ toSub-∷[] x (` y) ⟩
  ` y ⟪ flexFlex-≢ ¬p ⟫ₐ
    ∎

flexRigid∉-Unifies
  : (x : Fin (suc m)) (t : Tm (suc m))  (x∉ : x ∉ₜ t)
  → Unifiesₐ t (` x) (flexRigid∉ x∉)
flexRigid∉-Unifies x t x∉ = begin
  t ⟪ flexRigid∉ x∉ ⟫ₐ
    ≡⟨⟩
  t ⟪ punchOutTm x∉ / x ∷ [] ⟫ₐ
    ≡⟨ toSub-∷[] x t ⟩
  t ⟪ punchOutTm x∉ for x ⟫
    ≡⟨ sub-for-nonfree=punchOut t x∉ ⟩
  punchOutTm x∉
    ≡⟨ sym $ sub-for-x-in-x x ⟩
  ` x ⟪ (punchOutTm x∉) for x ⟫
     ≡⟨ (sym $ toSub-∷[] x (` x)) ⟩
  ` x ⟪ flexRigid∉ x∉ ⟫ₐ
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
  → subⁿ σ (ts ʳ++ us) ≡ subⁿ σ ts ʳ++ subⁿ σ us
sub-ʳ++ []       us = refl
sub-ʳ++ (x ∷ ts) us = sub-ʳ++ ts (x ∷ us)

sub-▷
  : {σ : Sub m n} (ps : Steps m) (t : Tm m)
  → (ps ▷ t) ⟪ σ ⟫ ≡ ps ⟪ σ ⟫′ ▷ (t ⟪ σ ⟫)
sub-▷ []                          t = refl
sub-▷ {σ = σ} (step _ us ts ∷ ps) t =
  cong (λ ts → op′ _ ts) $ begin
    subⁿ σ (us ʳ++ ((ps ▷ t) ∷ ts))
      ≡⟨ sub-ʳ++ us _ ⟩
    subⁿ σ us ʳ++ (subⁿ σ ((ps ▷ t) ∷ ts))
      ≡⟨ cong (λ t → subⁿ σ us ʳ++ (t ∷ subⁿ σ ts)) (sub-▷ ps t) ⟩
    subⁿ σ us ʳ++ (((ps ⟪ σ ⟫′) ▷ (t ⟪ σ ⟫)) ∷ subⁿ σ ts)
      ∎

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
    ≡⟨ (sym $ +-assoc (size x) (sizeⁿ xs) (sizeⁿ ys)) ⟩
  (size x + sizeⁿ xs) + sizeⁿ ys
    ≡⟨ +-comm (size x + sizeⁿ xs) (sizeⁿ ys) ⟩
  sizeⁿ ys + (size x + sizeⁿ xs)
    ≡⟨ (sym $ size-ʳ++ ys (x ∷ xs)) ⟩
  sizeⁿ (ys ʳ++ (x ∷ xs))
    ∎
    
▷₁-size : (t : Tm m) (p : Step m)
  → t ≺ (p ▷₁ t)
▷₁-size t (step i ys xs) = ʳ++-size i ys t xs 

------------------------------------------------------------------------------
-- 
------------------------------------------------------------------------------

sub-ps=[] : {σ : Sub m n} {ps : Steps m} → ps ⟪ σ ⟫′ ≡ [] → ps ≡ []
sub-ps=[] { ps = [] } _ = refl

------------------------------------------------------------------------------
-- No Cycle Lemma
------------------------------------------------------------------------------

no-cycle
  : (t : Tm m) (ps : Steps m)
  → t ≡ ps ▷ t 
  → ps ≡ []
no-cycle t ps = no-cycle′ t ps (≺-wf t)
  where
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

unify-occurrence
  : (σ : Sub m n) {x : Fin m} {t : Tm m}
  → x ∈ₜ t → ` x ⟪ σ ⟫ ≡ t ⟪ σ ⟫ → t ≡ ` x
unify-occurrence σ {x} {t} x∈ eq = begin
  t
    ≡⟨ ▷walk=id x∈ ⟩
  ps ▷ ` x
    ≡⟨ cong (_▷ ` x) ps=[] ⟩
  [] ▷ ` x
    ≡⟨⟩
  ` x
  ∎ 
  where
    ps = walk x∈

    ps=[] : ps ≡ []
    ps=[] = sub-ps=[] $ no-cycle (t ⟪ σ ⟫) (ps ⟪ σ ⟫′) $ begin
      t ⟪ σ ⟫
        ≡⟨ cong _⟪ σ ⟫ (▷walk=id x∈) ⟩
      (ps ▷ ` x) ⟪ σ ⟫
        ≡⟨ sub-▷ ps (` x) ⟩
      ps ⟪ σ ⟫′ ▷ ` x ⟪ σ ⟫
        ≡⟨ cong ((ps ⟪ σ ⟫′) ▷_) eq ⟩
      ps ⟪ σ ⟫′ ▷ t ⟪ σ ⟫
        ∎

------------------------------------------------------------------------------
-- Correctness of amgu
------------------------------------------------------------------------------

flexFlex-Unifies
  : (x y : Fin m)
  → ∃[ l ] Σ[ σ ∈ AList m l ] Unifiesₐ (` x) (` y) σ
flexFlex-Unifies {suc m} x y with x ≟ y
... | yes refl = _ , [] , refl
... | no ¬p    = m , (flexFlex-≢ ¬p) , flexFlex≢-Unifies ¬p

flexRigid-UnifiesOrNot
  : (x : Fin m) (i : k ∈ D) (ts : Tm m ^ k)
  → Dec (∃[ l ] Σ[ σ ∈ AList m l ] Unifiesₐ (op′ i ts) (` x) σ)
flexRigid-UnifiesOrNot {suc m} x i ts with x ∈ₜ? op′ i ts
... | no x∉  = yes (m , flexRigid∉ x∉ , flexRigid∉-Unifies x (op′ i ts) x∉)
... | yes x∈ = no λ where
  (l , σ , p) →  var≢op x i ts (unify-occurrence (toSub σ) x∈ (sym p)) 

{-
mutual
  amgu⁺ : (t u : Tm m) (σ : AList m n)
    → Dec (∃[ l ] Σ[ ρ ∈ AList n l ] Unifiesₐ t u (σ ++ ρ))
  amgu⁺ (op′ i ts) (op′ j us) ρ with i ≟∈ j
  ... | no ¬p    = no λ where (_ , ρ , p) → ¬p (op-inj₁₂ p)
  ... | yes refl = {!!}
  amgu⁺ (` x)               (` y) []          = yes (flexFlex-Unifies x y)
  amgu⁺ t@(op (_ , i , ts)) (` y) []          = flexRigid-UnifiesOrNot y i ts
  amgu⁺ (` x)               u     []          = {!!}
  amgu⁺ t                   u     (r / z ∷ σ) with amgu⁺ (t ⟪ r for z ⟫) (u ⟪ r for z ⟫) σ
  ... | no ¬p = {!!}
  ... | yes (_ , ρ , p) = yes $ _ , ρ , (begin
    t ⟪ (r / z ∷ σ) ++ ρ ⟫ₐ
      ≡⟨ toSub-∷ z (σ ++ ρ) t ⟩
    t ⟪ r for z ⟫ ⟪ σ ++ ρ ⟫ₐ
      ≡⟨ p ⟩
    u ⟪ r for z ⟫ ⟪ σ ++ ρ ⟫ₐ
      ≡⟨ (sym $ toSub-∷ z (σ ++ ρ) u) ⟩
    u ⟪ (r / z ∷ σ) ++ ρ ⟫ₐ
      ∎)
-}
