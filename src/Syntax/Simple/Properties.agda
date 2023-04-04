{-# OPTIONS --with-K  #-}

open import Prelude
  hiding (_++_; _+_)
open import Syntax.Simple.Description

module Syntax.Simple.Properties (D : Desc) where

open import Syntax.Simple.Term        D
open import Syntax.Simple.Association D
open import Syntax.Simple.Unification D

private variable
  Γ Δ Ξ m n l i j k : ℕ
  ts us   : Tm Ξ ^ n
  σ₁ σ₂   : Sub Γ Δ
  x y     : Fin Ξ

------------------------------------------------------------------------------
-- Trivial proofs

var≢op : (x : Fin m) (i : l ∈ D) (ts : Tm m ^ l)
  → ` x ≢ op (_ , i , ts)
var≢op x i ts ()

op-inj
  : {(l , i , ts) (k , j , us) : ⟦ D ⟧ (Tm Ξ)}
  → op′ i ts ≡ op′ j us
  → Σ (l ≡ k) λ where refl → Σ (i ≡ j) λ where refl → ts ≡ us
op-inj refl = refl , refl , refl

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
  where open ≡-Reasoning

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
  where open ≡-Reasoning
  
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
  where open ≡-Reasoning

------------------------------------------------------------------------------
-- Proofs about free variables

mutual
  ∈ₜ→∈fv : {x : Fin m} {t : Tm m} → x ∈ₜ t → x ∈ fv t
  ∈ₜ→∈fv (here p) = here p
  ∈ₜ→∈fv (ops p)  = ∈ₜ→∈fvⁿ p

  ∈ₜ→∈fvⁿ : {x : Fin m} {ts : Tm m ^ l} → x ∈ₜₛ ts → x ∈ fvⁿ ts
  ∈ₜ→∈fvⁿ (head x∈)     = ∈-++⁺ˡ        (∈ₜ→∈fv x∈)
  ∈ₜ→∈fvⁿ (tail {t = t} x∈) = ∈-++⁺ʳ (fv t) (∈ₜ→∈fvⁿ x∈)

mutual 
  ∈fv→∈ₜ : {x : Fin m} {t : Tm m} → x ∈ fv t → x ∈ₜ t
  ∈fv→∈ₜ {t = ` x}  (here px) = here px
  ∈fv→∈ₜ {t = op _} x∈        = ops $ ∈fv→∈ₜⁿ x∈

  ∈fv→∈ₜⁿ : {x : Fin m} {ts : Tm m ^ l} → x ∈ fvⁿ ts → x ∈ₜₛ ts
  ∈fv→∈ₜⁿ {x} {l = suc l} {ts = t ∷ ts} x∈ with ∈-++⁻ (fv t) x∈
  ... | inl x∈t  = head (∈fv→∈ₜ x∈t)
  ... | inr x∈ts = tail (∈fv→∈ₜⁿ x∈ts)
{-
mutual
  checkFv : (x : Fin m) (t : Tm m) → Dec (x ∈ fv t)
  checkFv x (` y)  with x ≟ y
  ... | yes p = yes (here p)
  ... | no ¬p = no λ where (here p) → ¬p p
  checkFv x (op (_ , _ , ts)) = checkFvⁿ x ts

  checkFvⁿ : (x : Fin m) (t : Tm m ^ l) → Dec (x ∈ fvⁿ t)
  checkFvⁿ {l = zero}  _ _        = no λ ()
  checkFvⁿ {l = suc l} x (t , ts) with checkFv x t
  ... | yes p = yes (∈-++⁺ˡ p)
  ... | no ¬p with checkFvⁿ x ts
  ... | yes q = yes (∈-++⁺ʳ (fv t) q)
  ... | no ¬q = no λ where x → case ∈-++⁻ (fv t) x of λ where
    (inl ∈t)  → ¬p ∈t
    (inr ∈ts) → ¬q ∈ts
-}

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

toSub-⨟
  : (ρ : AList m n) (σ : AList n l) 
  → (t : Tm m)
  → t ⟪ ρ ++ σ ⟫ₐ ≡ t ⟪ ρ ⟫ₐ ⟪ σ ⟫ₐ
toSub-⨟ []          σ t = cong _⟪ σ ⟫ₐ (sym $ sub-id t)
toSub-⨟ (u / x ∷ ρ) σ t = begin
  t ⟪ (u for x) ⨟ toSub (ρ ++ σ) ⟫
    ≡⟨ sub-assoc (u for x) (toSub (ρ ++ σ)) t ⟩
  t ⟪ u for x ⟫ ⟪ ρ ++ σ ⟫ₐ
    ≡⟨ toSub-⨟ ρ σ (t ⟪ u for x ⟫) ⟩
  t ⟪ u for x ⟫ ⟪ ρ ⟫ₐ ⟪ σ ⟫ₐ
    ≡⟨ cong (_⟪ σ ⟫ₐ) (sym $ sub-assoc (u for x) (toSub ρ) t) ⟩
  t ⟪ toSub (u / x ∷ ρ ) ⟫ ⟪ σ ⟫ₐ
    ∎
  where open ≡-Reasoning

toSub-/∷[]
  : {u : Tm m} (x : Fin (suc m))
  → (t : Tm (suc m))
  → t ⟪ u / x ∷ [] ⟫ₐ ≡ t ⟪ u for x ⟫
toSub-/∷[] {_} {u} x t = begin
  t ⟪ u / x ∷ [] ⟫ₐ
    ≡⟨ sub-assoc (u for x) ids t ⟩
  t ⟪ u for x ⟫ ⟪ ids ⟫
    ≡⟨ sub-id _ ⟩
  t ⟪ u for x ⟫
    ∎
  where open ≡-Reasoning

------------------------------------------------------------------------------
-- Proofs that amgu does provide a maximal general unifier

flexFlex-is-unifier
  : (x y : Fin m)
  → let σ = flexFlex x y .proj₂ in
    ` x ⟪ σ ⟫ₐ ≡ ` y ⟪ σ ⟫ₐ
flexFlex-is-unifier {m = suc m} x y with x ≟ y
... | yes refl = refl
... | no ¬p = begin
  ` x ⟪ flexFlex-≢ ¬p ⟫ₐ
    ≡⟨ toSub-/∷[] x (` x) ⟩
  ` x ⟪ (` punchOut ¬p) for x ⟫
    ≡⟨ punchOut-for-x≢y ¬p ⟩
  ` y ⟪ (` punchOut ¬p) for x ⟫
    ≡⟨ sym $ toSub-/∷[] x (` y) ⟩
  ` y ⟪ flexFlex-≢ ¬p ⟫ₐ
    ∎
  where open ≡-Reasoning

flexRigid∉-is-unifier
  : (x : Fin (suc m)) (t : Tm (suc m))  (x∉ : x ∉ₜ t)
  → let σ = flexRigid∉ x∉ in
    t ⟪ σ ⟫ₐ ≡ ` x ⟪ σ ⟫ₐ
flexRigid∉-is-unifier x t x∉ = begin
  t ⟪ flexRigid∉ x∉ ⟫ₐ
    ≡⟨⟩
  t ⟪ punchOutTm x∉ / x ∷ [] ⟫ₐ
    ≡⟨ toSub-/∷[] x t ⟩
  t ⟪ punchOutTm x∉ for x ⟫
    ≡⟨ sub-for-nonfree=punchOut t x∉ ⟩
  punchOutTm x∉
    ≡⟨ sym $ sub-for-x-in-x x ⟩
  ` x ⟪ (punchOutTm x∉) for x ⟫
     ≡⟨ (sym $ toSub-/∷[] x (` x)) ⟩
  ` x ⟪ flexRigid∉ x∉ ⟫ₐ
  ∎
  where open ≡-Reasoning

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
    → walk x∈ ▷ ` x ≡ t
  ▷walk=id (here refl)              = refl
  ▷walk=id (ops {_} {i} {t ∷ _} x∈) = ▷walks=id i t [] x∈ 

  ▷walks=id : (i : l ʳ+ (suc k) ∈ D)
    → (t : Tm m) (us : Tm m ^ l) {ts : Tm m ^ k}
    → (x∈ : x ∈ₜₛ t ∷ ts)
    → walkTms i t us ts x∈ ▷ ` x ≡ op′ i (us ʳ++ (t ∷ ts))
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
  where open ≡-Reasoning

no-cycle
  : (t : Tm m) (ps : Steps m)
  → t ≡ ps ▷ t 
  → ps ≡ []
no-cycle t ps = no-cycle′ t ps (≺-wf t)

  where
    no-cycle′
      : (t : Tm m) (ps : Steps m) → Acc _≺_ t
      → t ≡ ps ▷ t 
      → ps ≡ []
    no-cycle′ _                   []                      ac _ = refl
    no-cycle′ (op (l , pos , vs)) (step {j} k us ts ∷ ps) (acc g) p with op-inj p
    ... | refl , refl , eq with splitAt j vs
    ... | ys , x ∷ zs , refl with ▷₁-size x (step k ys zs)
    ... | x< = ⊥-elim₀ $ [xs]≢[] _ $ no-cycle′ x (ps L.++ _) (g x x<) x=ps▷p▷x
      where
        open ≡-Reasoning
        x=ps▷p▷x = begin
          x
            ≡⟨ V.∷-injectiveˡ $ ʳ++-≡ ys us eq .proj₂ ⟩
          ps ▷ step k ys zs ▷₁ x
            ≡⟨ ++-▷▷₁ ps (step k ys zs) x ⟩
          ps L.++ L.[ step k ys zs ] ▷ x
          ∎
