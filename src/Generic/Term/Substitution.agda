-- {-# OPTIONS --with-K #-}

open import Prelude
  hiding (subst)
open import Generic.Signature

module Generic.Term.Substitution (Ds : ConDs) where

open import Language.Type
open import Generic.Term.Base     Ds
open import Generic.Term.Fold     Ds
open import Generic.Term.Renaming Ds

private
  variable
    n     : ℕ
    Γ Δ Ξ : Type
    Ds′   : ConDs

exts : (Γ → Term Δ) → Γ ⁺ → Term (Δ ⁺)
exts f z     = ` z
exts f (s x) = rename s_ (f x)

exts-ids=ids
  : (x : (Γ ⁺))
  → exts `_ x ≡ ` x
exts-ids=ids z     = refl
exts-ids=ids (s x) = refl

Sub : (Γ Δ : Type) → Type
Sub Γ Δ = Γ → Term Δ

mutual
  {-# TERMINATING #-}
  subst : Sub Γ Δ → Term Γ → Term Δ
  subst f (` x)  = f x
  subst f (op t) = op (substMap Ds f t)

  substMap : (Ds′ : ConDs) → Sub Γ Δ → ⟦ Ds′ ⟧ Term Γ → ⟦ Ds′ ⟧ Term Δ
  substMap (D ∷ [])         f t       = substMapᶜ D f t
  substMap (D ∷ _ ∷ _)      f (inl t) = inl (substMapᶜ D f t)
  substMap (_ ∷ Ds@(_ ∷ _)) f (inr t) = inr (substMap Ds f t)

  substMapᶜ : (D : ConD) → Sub Γ Δ → ⟦ D ⟧ᶜ Term Γ → ⟦ D ⟧ᶜ Term Δ
  substMapᶜ ι       f _       = tt
  substMapᶜ (σ A D) f (a , t) = a , substMapᶜ (D a) f t
  substMapᶜ (ρ R D) f (t , u) = substMapʳ R f t , substMapᶜ D f u

  substMapʳ : (R : RecD) → Sub Γ Δ → ⟦ R ⟧ʳ Term Γ → ⟦ R ⟧ʳ Term Δ
  substMapʳ ι     f t = subst f t
  substMapʳ (δ R) f t = substMapʳ R (exts f) t

infixl 5 ⟪_⟫_

⟪_⟫_ : (f : Γ → Term Δ) → Term Γ → Term Δ
⟪_⟫_ = subst

_⨟_ : Sub Γ Δ → Sub Δ Ξ → Sub Γ Ξ
(f ⨟ g) x = ⟪ g ⟫ f x

subst-var=id : (f : Sub Γ Δ)
  → (x : Γ)
  → ⟪ f ⟫ ` x ≡ f x  
subst-var=id f x = refl

mutual
  {-# TERMINATING #-}
  var-subst=id : (t : Term Γ)
    → ⟪ `_ ⟫ t ≡ t
  var-subst=id (`  x) = refl
  var-subst=id (op t) = cong op (var-subst=idMap Ds t)

  var-subst=idMap : (Ds′ : ConDs)
    → (t : ⟦ Ds′ ⟧ Term Γ)
    → substMap Ds′ `_ t ≡ t
  var-subst=idMap (D ∷ [])         t       = var-subst=idMapᶜ D t
  var-subst=idMap (D ∷ Ds@(_ ∷ _)) (inl t) = cong inl (var-subst=idMapᶜ D t)
  var-subst=idMap (D ∷ Ds@(_ ∷ _)) (inr x) = cong inr (var-subst=idMap Ds x)

  var-subst=idMapᶜ : (D : ConD)
    → (t : ⟦ D ⟧ᶜ Term Γ)
    → substMapᶜ D `_ t ≡ t
  var-subst=idMapᶜ ι       _       = refl
  var-subst=idMapᶜ (σ A D) (a , t) = cong (a ,_) (var-subst=idMapᶜ (D a) t)
  var-subst=idMapᶜ (ρ R D) (t , u) = cong₂ _,_ (var-subst=idMapʳ R t) (var-subst=idMapᶜ D u)

  var-subst=idMapʳ : (R : RecD)
    → (t : ⟦ R ⟧ʳ Term Γ)
    → substMapʳ R `_ t ≡ t
  var-subst=idMapʳ ι     t = var-subst=id t
  var-subst=idMapʳ (δ R) t = begin
    substMapʳ R (exts `_) t
      ≡[ i ]⟨ substMapʳ R (λ x → exts-ids=ids x i) t ⟩
    substMapʳ R `_ t
      ≡⟨ var-subst=idMapʳ R t ⟩
    t ∎
    where open ≡-Reasoning

punchesIn
  : ∀ n
  → Sub Γ Δ
  → Sub (Γ ^ n) (Δ ^ n)
punchesIn zero    f x = f x
punchesIn (suc n) f z     = ` z
punchesIn (suc n) f (s x) = ⟨ s_ ⟩ punchesIn n f x

exts-punchesIn=punchesIn
  : {n : ℕ} {f : Sub Γ Δ}
  → (x : Γ ^ n ⁺)
  → exts (punchesIn n f) x ≡ punchesIn (suc n) f x
exts-punchesIn=punchesIn z     = refl
exts-punchesIn=punchesIn (s x) = refl

punchesIn-punchIn-comm
  : {f : Sub Γ Δ}
  → (n : ℕ)
  → (x : Γ ^ n)
  → punchesIn n (exts f) (punchIn n x) ≡ ⟨ punchIn n ⟩ punchesIn n f x
punchesIn-punchIn-comm zero    x = refl
punchesIn-punchIn-comm (suc n) z     = refl
punchesIn-punchIn-comm {f = f} (suc n) (s x) = begin
  ⟨ s_ ⟩ punchesIn n (exts _) (punchIn n x)
    ≡⟨ cong (rename s_) (punchesIn-punchIn-comm n x) ⟩
  ⟨ s_ ⟩ ⟨ punchIn n ⟩ punchesIn n f x
    ≡⟨ rename-comp (punchIn n) s_ (punchesIn n f x) ⟩
  ⟨ s_ ∘ punchIn n ⟩ punchesIn n f x
    ≡⟨ refl ⟩
  ⟨ punchIn (suc n) ∘ s_ ⟩ punchesIn n f x
    ≡⟨ sym (rename-comp s_ (punchIn (suc n)) (punchesIn n f x)) ⟩
  ⟨ punchIn (suc n) ⟩ (⟨ s_ ⟩ punchesIn n _ x)
    ∎
  where open ≡-Reasoning

mutual
  {-# TERMINATING #-}
  punchIn-punchesIn-comm
    : (f : Sub Γ Δ)
    → (t : Term (Γ ^ n))
    → ⟪ punchesIn n (exts f) ⟫ ⟨ punchIn n ⟩ t ≡ ⟨ punchIn n ⟩ ⟪ punchesIn n f ⟫ t
  punchIn-punchesIn-comm f (` x)  = punchesIn-punchIn-comm _ x
  punchIn-punchesIn-comm f (op t) = cong op (punchIn-punchesIn-commMap Ds f t)

  punchIn-punchesIn-commMap 
    : (Ds′ : ConDs)
    → (f : Sub Γ Δ)
    → (t : ⟦ Ds′ ⟧ Term (Γ ^ n))
    → substMap Ds′ (punchesIn n (exts f)) (renameMap Ds′ (punchIn n) t)
      ≡ renameMap Ds′ (punchIn n) (substMap Ds′ (punchesIn n f) t)
  punchIn-punchesIn-commMap (D ∷ [])         f t       = punchIn-punchesIn-commMapᶜ D f t
  punchIn-punchesIn-commMap (D ∷ _ ∷ _)      f (inl t) = cong inl (punchIn-punchesIn-commMapᶜ D f t)
  punchIn-punchesIn-commMap (D ∷ Ds@(_ ∷ _)) f (inr t) = cong inr (punchIn-punchesIn-commMap Ds f t)

  punchIn-punchesIn-commMapᶜ
    : (D : ConD)
    → (f : Sub Γ Δ)
    → (t : ⟦ D ⟧ᶜ Term (Γ ^ n))
    → substMapᶜ D (punchesIn n (exts f)) (renameMapᶜ D (punchIn n) t)
      ≡ renameMapᶜ D (punchIn n) (substMapᶜ D (punchesIn n f) t)
  punchIn-punchesIn-commMapᶜ ι       _ _       = refl
  punchIn-punchesIn-commMapᶜ (σ A D) f (a , t) = cong₂ _,_ refl (punchIn-punchesIn-commMapᶜ (D a) f t)
  punchIn-punchesIn-commMapᶜ (ρ R D) f (t , u) = cong₂ _,_
    (punchIn-punchesIn-commMapʳ R f t) (punchIn-punchesIn-commMapᶜ D f u)

  punchIn-punchesIn-commMapʳ
    : (R : RecD)
    → (f : Sub Γ Δ)
    → (t : ⟦ R ⟧ʳ Term (Γ ^ n))
    → substMapʳ R (punchesIn n (exts f)) (renameMapʳ R (punchIn n) t)
      ≡ renameMapʳ R (punchIn n) (substMapʳ R (punchesIn n f) t)
  punchIn-punchesIn-commMapʳ ι     f t = punchIn-punchesIn-comm f t
  punchIn-punchesIn-commMapʳ {n = n} (δ R) f t = begin
    substMapʳ R (exts (punchesIn _ (exts f))) (renameMapʳ R (ext (punchIn _)) t)
      ≡⟨ cong (substMapʳ R (exts (punchesIn _ (exts f)))) (cong₂ (renameMapʳ R) (funExt (ext-punchIn=punchIn n)) refl) ⟩
    substMapʳ R (exts (punchesIn _ (exts f))) (renameMapʳ R (punchIn (suc n)) t)
      ≡[ i ]⟨ substMapʳ R (λ x → exts-punchesIn=punchesIn {n = n} {f = exts f} x i)  (renameMapʳ R (punchIn (suc n)) t) ⟩
    substMapʳ R (punchesIn (suc n) (exts f)) (renameMapʳ R (punchIn (suc n)) t)
      ≡⟨ punchIn-punchesIn-commMapʳ R f t ⟩
    renameMapʳ R (punchIn (suc n)) (substMapʳ R (punchesIn (suc n) f) t)
      ≡[ i ]⟨ renameMapʳ R (λ x → ext-punchIn=punchIn n x (~ i)) (substMapʳ R (punchesIn (suc n) f) t) ⟩
    renameMapʳ R (ext (punchIn n)) (substMapʳ R (punchesIn (suc n) f) t)
      ≡[ i ]⟨ renameMapʳ R (ext (punchIn n)) (substMapʳ R (λ x → exts-punchesIn=punchesIn {n = n} {f = f} x (~ i)) t) ⟩
    renameMapʳ R (ext (punchIn n)) (substMapʳ R (exts (punchesIn _ f)) t)
      ∎
    where open ≡-Reasoning

weakening-subst-comm
  : (f : Sub Γ Δ)
  → (t : Term Γ)
  → ⟪ exts f ⟫ ⟨ s_ ⟩ t ≡ ⟨ s_ ⟩ ⟪ f ⟫ t
weakening-subst-comm = punchIn-punchesIn-comm

ren-ext-comm
  : (f : Γ → Δ)
  → (x : Γ ⁺)
  → ` ext f x ≡ exts (`_ ∘ f) x
ren-ext-comm f z     = refl
ren-ext-comm f (s x) = refl

exts-subst : (f : Sub Γ Δ) (g : Sub Δ Ξ)
  → (x : Γ ⁺) 
  → (exts f ⨟ exts g) x ≡ exts (f ⨟ g) x
exts-subst f g z     = refl
exts-subst f g (s x) = weakening-subst-comm g (f x)

mutual
  {-# TERMINATING #-}
  subst-assoc
    : (f : Sub Γ Δ) (g : Sub Δ Ξ)
    → (t : Term Γ)
    → ⟪ g ⟫ ⟪ f ⟫ t ≡ ⟪ f ⨟ g ⟫ t
  subst-assoc f g (` x)  = refl
  subst-assoc f g (op t) = cong op (subst-assocMap Ds f g t)

  subst-assocMap
    : (Ds : ConDs)
    → (f : Sub Γ Δ) (g : Sub Δ Ξ)
    → (t : ⟦ Ds ⟧ Term Γ)
    → substMap Ds g (substMap Ds f t) ≡ substMap Ds (f ⨟ g) t
  subst-assocMap (D ∷ [])         f g t       = subst-assocMapᶜ D f g t
  subst-assocMap (D ∷ (_ ∷ _))    f g (inl t) = cong inl (subst-assocMapᶜ D f g t)
  subst-assocMap (_ ∷ Ds@(_ ∷ _)) f g (inr t) = cong inr (subst-assocMap Ds f g t)

  subst-assocMapᶜ
    : (D : ConD)
    → (f : Sub Γ Δ) (g : Sub Δ Ξ)
    → (t : ⟦ D ⟧ᶜ Term Γ)
    → substMapᶜ D g (substMapᶜ D f t) ≡ substMapᶜ D (f ⨟ g) t
  subst-assocMapᶜ ι       f g t = refl
  subst-assocMapᶜ (σ A D) f g (a , t) = cong (a ,_) (subst-assocMapᶜ (D a) f g t)
  subst-assocMapᶜ (ρ R D) f g (t , u) = cong₂ _,_ (subst-assocMapʳ R f g t) (subst-assocMapᶜ D f g u)

  subst-assocMapʳ
    : (D : RecD)
    → (f : Sub Γ Δ) (g : Sub Δ Ξ)
    → (t : ⟦ D ⟧ʳ Term Γ)
    → substMapʳ D g (substMapʳ D f t) ≡ substMapʳ D (f ⨟ g) t
  subst-assocMapʳ ι     f g t = subst-assoc f g t
  subst-assocMapʳ (δ D) f g t = begin
    substMapʳ D (exts g) (substMapʳ D (exts f) t)
      ≡⟨ subst-assocMapʳ D (exts f) (exts g) t ⟩
    substMapʳ D (exts f ⨟ exts g) t
      ≡[ i ]⟨ substMapʳ D (λ x → exts-subst f g x i) t ⟩
    substMapʳ D (exts (f ⨟ g)) t
      ∎
    where open ≡-Reasoning
