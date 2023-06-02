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
  t u v   : Tm Ξ

------------------------------------------------------------------------------
-- Trivial proofs

var≢op : {x : Fin m} {i : l ∈ D} {ts : Tm m ^ l}
  → op (_ , i , ts) ≢ ` x
var≢op ()

op≢var : {x : Fin m} {i : l ∈ D} {ts : Tm m ^ l}
  → ` x ≢ op (_ , i , ts)
op≢var()

op-inj
  : {(l , i , ts) (k , j , us) : ⟦ D ⟧ (Tm Ξ)}
  → _≡_ {A = Tm _ } (op (l , i , ts)) (op (k , j , us))
  → Σ (l ≡ k) λ where refl → Σ (i ≡ j) λ where refl → ts ≡ us
op-inj refl = refl , refl , refl

op-inj₁₂
  : {(l , i , ts) (k , j , us) : ⟦ D ⟧ (Tm Ξ)}
  → _≡_ {A = Tm _ } (op (l , i , ts)) (op (k , j , us))
  → (l , i) ≡ (k , j)
op-inj₁₂ refl = refl

op-inj₃
  : {i : n ∈ D} {ts us : Tm Ξ ^ n}
  → op′ i ts ≡ op′ i us
  → ts ≡ us
op-inj₃ refl = refl

op-cong⇔ : {i : k ∈ D}
  → (ts ≡ us) ⇔ (op′ i ts ≡ op′ i us)
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

------------------------------------------------------------------------------
-- Proofs about ⟨ t for x ⟩

opaque
  unfolding sub-for
  
  sub-t-for-x-x
    : sub-for t x x ≡ t
  sub-t-for-x-x {Ξ} {t} {x = x} with x ≟ x
  ... | yes p = refl
  ... | no ¬p = ⊥-elim₀ (¬p refl)

  x⟨t/x⟩=t : (x : Fin (suc m))
    → ` x ⟨ t for x ⟩ ≡ t
  x⟨t/x⟩=t {_} {t} x = begin
    ` x ⟨ t for x ⟩
      ≡⟨ lookup∘tabulate (sub-for t x) x ⟩
    sub-for t x x
      ≡⟨ sub-t-for-x-x ⟩
    t
      ∎

  sub-t-for-x-y
    : (¬p : x ≢ y)
    → sub-for t x y ≡ ` punchOut ¬p 
  sub-t-for-x-y {x = x} {y} ¬p with x ≟ y
  ... | yes p = ⊥-elim₀ (¬p p)
  ... | no ¬p = refl

  y⟨t/x⟩=y : {t : Tm m} {x y : Fin (suc m)}
    → (¬p : x ≢ y)
    → ` y ⟨ t for x ⟩ ≡ ` punchOut ¬p
  y⟨t/x⟩=y {m} {t} {x} {y} ¬p = begin
    ` y ⟨ t for x ⟩
      ≡⟨ lookup∘tabulate (sub-for t x) y ⟩
    sub-for t x y
      ≡⟨ sub-t-for-x-y ¬p ⟩
    ` F.punchOut ¬p
      ∎

module _ {m : ℕ} where
  punchOut-for-x≢y
    : {x y : Fin (suc m)}
    → (¬p : x ≢ y)
    → ` x ⟨ (` punchOut ¬p) for x ⟩ ≡ ` y ⟨ (` punchOut ¬p) for x ⟩
  punchOut-for-x≢y {x = x} {y} ¬p = begin
    ` x ⟨ (` punchOut ¬p) for x ⟩
      ≡⟨ x⟨t/x⟩=t x ⟩
    ` punchOut ¬p
      ≡⟨ (sym $ y⟨t/x⟩=y ¬p) ⟩
    ` y ⟨ (` punchOut ¬p) for x ⟩
      ∎

------------------------------------------------------------------------------
-- punchInTm and punchOutTm
module _ {m : ℕ} {x : Fin (suc m)} where
  mutual
    punchInTm-punchOutTm
      : (x∉ : x ∉ᵥ t)
      → punchInTm x (punchOutTm x∉) ≡ t
    punchInTm-punchOutTm {` y}      x∉ = cong `_ (punchIn-punchOut (x∉ ∘ here))
    {- cong `_ $ begin
      lookup (tabulate (punchIn x)) (punchOut (x∉ ∘ here))
        ≡⟨ lookup∘tabulate (punchIn x) _ ⟩
      punchIn x (punchOut (x∉ ∘ here))
        ≡⟨ punchIn-punchOut _ ⟩
      y
        ∎
        -}
    punchInTm-punchOutTm {op′ i ts} x∉ = cong (op′ i) (punchInTm-punchOutTmⁿ (x∉ ∘ op))

    punchInTm-punchOutTmⁿ
      : (x∉ : x ∉ᵥₛ ts)
      → punchInTmⁿ x (punchOutTmⁿ x∉) ≡ ts
    punchInTm-punchOutTmⁿ {ts = []}     x∉ = refl
    punchInTm-punchOutTmⁿ {ts = t ∷ ts} x∉ = cong₂ _∷_
      (punchInTm-punchOutTm (x∉ ∘ head)) (punchInTm-punchOutTmⁿ (λ z → x∉ (tail z)))

  mutual
    x∉punchInTm : (t : Tm m) → x ∉ᵥ punchInTm x t
    x∉punchInTm (` y)      (here eq) = F.punchInᵢ≢i x y (sym eq)
    {- (sym $ begin
      x
        ≡⟨ eq ⟩
      lookup (tabulate (punchIn x)) y
        ≡⟨ lookup∘tabulate (punchIn x) y ⟩
      punchIn x y ∎)
    -}
    x∉punchInTm (op′ i ts) (op x∈ts) = x∉punchInTmⁿ ts x∈ts

    x∉punchInTmⁿ : (ts : Tm m ^ l) → x ∉ᵥₛ punchInTmⁿ x ts
    x∉punchInTmⁿ []       ()
    x∉punchInTmⁿ (t ∷ ts) (head x∈) = x∉punchInTm t x∈
    x∉punchInTmⁿ (t ∷ ts) (tail x∈) = x∉punchInTmⁿ ts x∈

module _ {u : Tm m} {x : Fin (suc m)} where opaque
  unfolding sub-for
  mutual
    punchIn-t⟨u/x⟩=t : (t : Tm m)
      → punchInTm x t ⟨ u for x ⟩ ≡ t
    punchIn-t⟨u/x⟩=t (` y)      = begin
      punchInTm x (` y) ⟨ u for x ⟩
        ≡⟨⟩
      lookup (u for x) (punchIn x y)
        ≡⟨ lookup∘tabulate (sub-for u x) (punchIn x y) ⟩
      sub-for u x (punchIn x y)
        ≡⟨ sub-t-for-x-y {t = u} (punchInᵢ≢i x y ∘ sym) ⟩
      ` punchOut (punchInᵢ≢i x y ∘ sym)
        ≡⟨ cong `_ (punchOut-punchIn x) ⟩
      ` y
        ∎

    {- begin
      punchInTm x (` y) ⟨ u for x ⟩
        ≡⟨⟩
      ` lookup (tabulate (punchIn x)) y ⟨ u for x ⟩
        ≡⟨ cong (λ i → ` i ⟨ u for x ⟩) (lookup∘tabulate (punchIn x) y) ⟩
      ` punchIn x y ⟨ u for x ⟩
        ≡⟨⟩
      lookup (tabulate (sub-for u x)) (punchIn x y)
        ≡⟨ lookup∘tabulate (sub-for u x) (punchIn x y) ⟩
      sub-for u x (punchIn x y)
        ≡⟨ sub-t-for-x-y {t = u} (punchInᵢ≢i x y ∘ sym) ⟩
      ` punchOut (punchInᵢ≢i x y ∘ sym)
        ≡⟨ cong `_ (punchOut-punchIn x) ⟩
      ` y
        ∎
        -}
    punchIn-t⟨u/x⟩=t (op′ i ts) = cong (op′ i) (punchIn-t⟨u/x⟩=tⁿ ts)

    punchIn-t⟨u/x⟩=tⁿ : (ts : Tm m ^ l)
      → punchInTmⁿ x ts ⟨ u for x ⟩ ≡ ts
    punchIn-t⟨u/x⟩=tⁿ []       = refl
    punchIn-t⟨u/x⟩=tⁿ (t ∷ ts) = cong₂ _∷_ (punchIn-t⟨u/x⟩=t t) (punchIn-t⟨u/x⟩=tⁿ ts)

  mutual
    t⟨u/x⟩=punchOut : {t : Tm (suc m)} (x∉ : x ∉ᵥ t)
      → t ⟨ u for x ⟩ ≡ punchOutTm x∉
    t⟨u/x⟩=punchOut {t} x∉ = begin
      t ⟨ u for x ⟩
        ≡⟨ cong _⟨ u for x ⟩ (sym (punchInTm-punchOutTm x∉)) ⟩
      punchInTm x (punchOutTm x∉) ⟨ u for x ⟩
        ≡⟨ punchIn-t⟨u/x⟩=t (punchOutTm x∉) ⟩
      punchOutTm x∉
        ∎
------------------------------------------------------------------------------
-- Occurrence check

++-▷ : (ps qs : Steps n) (t : Tm n)
  → ps L.++ qs ▷ t ≡ ps ▷ qs ▷ t
++-▷ []                 qs t = refl
++-▷ (step i us ts ∷ ps) qs t = 
  cong (λ u → op (_ , i , us ʳ++ (u ∷ ts))) (++-▷ ps qs t) 

++-▷▷₁ : (ps : Steps n) (p : Step n) (t : Tm n)
  → ps ▷ (p ▷₁ t) ≡ ps L.++ L.[ p ] ▷ t
++-▷▷₁ []       p₀ t = refl
++-▷▷₁ (p ∷ ps) p₀ t = cong (p ▷₁_) (++-▷▷₁ ps p₀ t)

module _ {m : ℕ} {x : Fin m} where mutual
  ▷walk=id : {t : Tm m} → (x∈ : x ∈ᵥ t)
    → t ≡ walk x∈ ▷ ` x
  ▷walk=id (here refl)              = refl
  ▷walk=id (op {_} {i} {t ∷ _} x∈) = ▷walks=id i t [] x∈ 

  ▷walks=id : (i : l ʳ+ (suc k) ∈ D)
    → (t : Tm m) (us : Tm m ^ l) {ts : Tm m ^ k}
    → (x∈ : x ∈ᵥₛ t ∷ ts)
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

unify-occur
  : (σ : Sub m n) {x : Fin m} {t : Tm m}
  → x ∈ᵥ t
  → ` x ⟨ σ ⟩ ≡ t ⟨ σ ⟩
  → ` x ≡ t
unify-occur σ {x} {t} x∈ eq =
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
  in sym $ begin
    t
      ≡⟨ ▷walk=id x∈ ⟩
    ps ▷ ` x
      ≡⟨ cong (_▷ ` x) ps=[] ⟩
    [] ▷ ` x
      ≡⟨⟩
    ` x
    ∎ 
