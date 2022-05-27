open import Prelude
open import Generic.Signature

module Generic.Term.Renaming (Ds : ConDs) where

open import Language.Type
open import Generic.Term.Base Ds

private
  variable
    Γ Δ Ξ : Type

mutual
  {-# TERMINATING #-}
  rename : (f : Γ → Δ) → Term Γ → Term Δ
  rename f (` x)  = ` f x
  rename f (op x) = op (renameMap Ds f x)

  renameMap : (Ds′ : ConDs) → (f : Γ → Δ) → ⟦ Ds′ ⟧ Term Γ → ⟦ Ds′ ⟧ Term Δ
  renameMap (D ∷ [])         f x       = renameMapᶜ D f x
  renameMap (D ∷ Ds@(_ ∷ _)) f (inl x) = inl (renameMapᶜ D f x)
  renameMap (D ∷ Ds@(_ ∷ _)) f (inr x) = inr (renameMap Ds f x)

  renameMapᶜ : (D : ConD) → (f : Γ → Δ) → ⟦ D ⟧ᶜ Term Γ → ⟦ D ⟧ᶜ Term Δ
  renameMapᶜ ι       f  _      = tt
  renameMapᶜ (σ A D) f (a , t) = a , renameMapᶜ (D a) f t
  renameMapᶜ (ρ R D) f (t , u) = renameMapʳ R f t , renameMapᶜ D f u

  renameMapʳ : (R : RecD) → (f : Γ → Δ) → ⟦ R ⟧ʳ Term Γ → ⟦ R ⟧ʳ Term Δ
  renameMapʳ ι     f t = rename f t 
  renameMapʳ (δ R) f t = renameMapʳ R (ext f) t

infixl 5 ⟨_⟩_
⟨_⟩_ = rename

mutual
  {-# TERMINATING #-}
  rename-id=id
    : (t : Term Γ)
    → ⟨ id ⟩ t ≡ t
  rename-id=id (`  x) = refl
  rename-id=id (op t) = cong op (rename-id=idMap Ds t)

  rename-id=idMap : (Ds′ : ConDs)
    → (t : ⟦ Ds′ ⟧ Term Γ)
    → renameMap Ds′ id t ≡ t
  rename-id=idMap (D ∷ [])         t       = rename-id=idMapᶜ D t
  rename-id=idMap (D ∷ Ds@(_ ∷ _)) (inl t) = cong inl (rename-id=idMapᶜ D t)
  rename-id=idMap (D ∷ Ds@(_ ∷ _)) (inr t) = cong inr (rename-id=idMap Ds t)

  rename-id=idMapᶜ : (D : ConD)
    → (t : ⟦ D ⟧ᶜ Term Γ)
    → renameMapᶜ D id t ≡ t
  rename-id=idMapᶜ ι       _       = refl
  rename-id=idMapᶜ (σ A D) (a , t) = cong₂ _,_ refl (rename-id=idMapᶜ (D a) t)
  rename-id=idMapᶜ (ρ R D) (t , u) = cong₂ _,_ (rename-id=idMapʳ R t) (rename-id=idMapᶜ D u)

  rename-id=idMapʳ : (R : RecD)
    → (t : ⟦ R ⟧ʳ Term Γ)
    → renameMapʳ R id t ≡ t
  rename-id=idMapʳ ι     t = rename-id=id t
  rename-id=idMapʳ (δ D) t = begin
    renameMapʳ D (ext id) t
      ≡[ i ]⟨ renameMapʳ D (λ x → ext-id=id x i) t ⟩
    renameMapʳ D id t
      ≡⟨ rename-id=idMapʳ D t ⟩
    t ∎
    where open ≡-Reasoning

mutual
  {-# TERMINATING #-}
  rename-comp
    : (f : Γ → Δ) (g : Δ → Ξ)
    → (t : Term Γ)
    → ⟨ g ⟩ ⟨ f ⟩ t ≡ ⟨ g ∘ f ⟩ t
  rename-comp f g (` x)  = refl
  rename-comp f g (op t) = cong op (rename-compMap Ds f g t)

  rename-compMap
    : (Ds′ : ConDs)
    → (f : Γ → Δ) (g : Δ → Ξ)
    → (t : ⟦ Ds′ ⟧ Term Γ)
    → renameMap Ds′ g (renameMap Ds′ f t) ≡ renameMap Ds′ (g ∘ f) t 
  rename-compMap (D ∷ [])         f g t       = rename-compMapᶜ D f g t
  rename-compMap (D ∷ Ds@(_ ∷ _)) f g (inl t) = cong inl (rename-compMapᶜ D f g t)
  rename-compMap (D ∷ Ds@(_ ∷ _)) f g (inr t) = cong inr (rename-compMap Ds f g t)

  rename-compMapᶜ
    : (D : ConD)
    → (f : Γ → Δ) (g : Δ → Ξ)
    → (t : ⟦ D ⟧ᶜ Term Γ)
    → renameMapᶜ D g (renameMapᶜ D f t) ≡ renameMapᶜ D (g ∘ f) t 
  rename-compMapᶜ ι       f g _       = refl
  rename-compMapᶜ (σ A D) f g (a , t) = cong₂ _,_ refl (rename-compMapᶜ (D a) f g t)
  rename-compMapᶜ (ρ R D) f g (t , u) = cong₂ _,_ (rename-compMapʳ R f g t) (rename-compMapᶜ D f g u)

  rename-compMapʳ
    : (R : RecD)
    → (f : Γ → Δ) (g : Δ → Ξ)
    → (t : ⟦ R ⟧ʳ Term Γ)
    → renameMapʳ R g (renameMapʳ R f t) ≡ renameMapʳ R (g ∘ f) t 
  rename-compMapʳ ι     f g t = rename-comp f g t
  rename-compMapʳ (δ R) f g t = begin
    renameMapʳ R (ext g) (renameMapʳ R (ext f) t)
      ≡⟨ rename-compMapʳ R (ext f) (ext g) t ⟩
    renameMapʳ R (ext g ∘ ext f) t
      ≡[ i ]⟨ renameMapʳ R (λ x → ext-assoc f g x i) t ⟩
    renameMapʳ R (ext (g ∘ f)) t
      ∎ 
    where open ≡-Reasoning
