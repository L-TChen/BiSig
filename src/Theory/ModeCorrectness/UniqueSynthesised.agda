import Syntax.Simple.Signature          as S
import Syntax.BiTyped.Signature         as B
import Theory.ModeCorrectness.Signature as MC

module Theory.ModeCorrectness.UniqueSynthesised
  {SD : S.SigD} (D : B.SigD SD) (mc : MC.ModeCorrect SD D) where

open import Prelude

open MC SD
open B  SD

open import Syntax.Simple  SD
open import Syntax.Context SD

open import Syntax.BiTyped.Functor   SD
import      Syntax.Typed.Raw.Functor SD as R

open import Theory.Erasure

open import Syntax.BiTyped.Term          D
open import Syntax.Typed.Raw.Term (erase D)

import Theory.ModeCorrectness.Functor SD as M

private variable
  Ξ     : ℕ
  xs    : Fins# Ξ
  Γ     : Cxt 0
  A B   : TExp  Ξ
  As    : TExps Ξ
  ρ₁ ρ₂ : TSub  Ξ 0

------------------------------------------------------------------------------
-- Uniqueness of Synthesised Types

uniq-⇒-var : (i : A ∈ Γ) (j : B ∈ Γ) → L.index i ≡ L.index j → A ≡ B
uniq-⇒-var (here refl) (here refl) _  = refl
uniq-⇒-var (there i)   (there j)   eq = uniq-⇒-var i j (F.suc-injective eq)

mutual

  uniq-⇒
    : {r : Raw (length Γ)}
    → (⊢t : Γ ⊢ r ⇒ A) (⊢u : Γ ⊢ r ⇒ B)
    → A ≡ B
  uniq-⇒ (var i ieq) (var j jeq) = uniq-⇒-var i j (trans ieq (sym jeq))
  uniq-⇒ (A ∋ t) (.A ∋ u) = refl
  uniq-⇒ {r = op (i , rs)} (op (deq , _ , refl , ts)) (op (_ , _ , refl , us)) =
    uniq-⇒ᶜ (SigD.ar D i) deq (mc i) ts us

  uniq-⇒ᶜ
    : (D@(ι d A Ds) : OpD) → d ≡ Syn → ModeCorrectᶜ D
    → ∀ {rs ρ₁ ρ₂}
    → ⟦ Ds ⟧ᵃˢ Raw _⊢_[_]_ ρ₁ Γ rs
    → ⟦ Ds ⟧ᵃˢ Raw _⊢_[_]_ ρ₂ Γ rs
    → A ⟨ ρ₁ ⟩ ≡ A ⟨ ρ₂ ⟩
  uniq-⇒ᶜ (ι Syn A Ds) refl (⊆xs , SDs) ts us =
    ≡-fv A λ x → uniq-⇒ⁿ Ds SDs ts us (⊆xs _)

  uniq-⇒ⁿ
    : (Ds : ArgsD Ξ) → ModeCorrectᵃˢ [] Ds
    → {rs : R.⟦ eraseᵃˢ Ds ⟧ᵃˢ Raw (length Γ)}
    → (ts : ⟦ Ds ⟧ᵃˢ Raw _⊢_[_]_ ρ₁ Γ rs)
    → (us : ⟦ Ds ⟧ᵃˢ Raw _⊢_[_]_ ρ₂ Γ rs)
    → ∀ {x} → x #∈ (known Ds)
    → ρ₁ x ≡ ρ₂ x
  uniq-⇒ⁿ []                  _         _         _         ()
  uniq-⇒ⁿ (_ ⊢[ Chk ] _ ∷ Ds) (_ , SDs) (_ , ⊢ts) (_ , ⊢us) =
    uniq-⇒ⁿ Ds SDs ⊢ts ⊢us
  uniq-⇒ⁿ (Δ ⊢[ Syn ] A ∷ Ds) (SD , SDs) (⊢t , ⊢ts) (⊢u , ⊢us) x∈ with ∈-∪⁻ (vars A) x∈
  ... | inl x∈A  = uniq-⇒ᵃ A Δ SD ⊢t ⊢u (uniq-⇒ⁿ Ds SDs ⊢ts ⊢us) x∈A
  ... | inr x∈Ds = uniq-⇒ⁿ Ds SDs ⊢ts ⊢us x∈Ds

  uniq-⇒ᵃ
    : (C : TExp Ξ) (Δ : TExps Ξ) → Cover xs Δ
    → {r : R.⟦ Δ ⟧ᵃ Raw (length Γ)}
    → (t : ⟦ Δ ⟧ᵃ Raw (_⊢_[ Syn ] (C ⟨ ρ₁ ⟩)) ρ₁ Γ r)
    → (u : ⟦ Δ ⟧ᵃ Raw (_⊢_[ Syn ] (C ⟨ ρ₂ ⟩)) ρ₂ Γ r)
    → (∀ {x} → x #∈ xs → ρ₁ x ≡ ρ₂ x)
    → ∀ {x} → x #∈ vars C
    → ρ₁ x ≡ ρ₂ x
  uniq-⇒ᵃ C []      _    ⊢t ⊢u f x = ≡-fv-inv C (uniq-⇒ ⊢t ⊢u) (∈vars→∈ᵥ x)
  uniq-⇒ᵃ C (A ∷ Δ) (A⊆xs ∷ Δ⊆xs) ⊢t ⊢u f =
    uniq-⇒ᵃ C Δ Δ⊆xs (subst (λ A → (⟦ Δ ⟧ᵃ _ _) _ (A ∷ _) _) A₁=A₂ ⊢t) ⊢u f
    where A₁=A₂ = ≡-fv A λ x∈ → f (A⊆xs (∈ᵥ→∈vars x∈))

¬switch
  : {r : Raw (length Γ)}
  → Γ ⊢ r ⇒ A
  → B ≢ A
  → ¬ Γ ⊢ r ⇐ B
¬switch ⊢t B≠A (⊢t′ ↑ B=A) rewrite uniq-⇒ ⊢t ⊢t′ = B≠A B=A
¬switch (op (d≡Syn , _)) B≠A (op (d≡Chk , _)) = Chk≢Syn (trans (sym d≡Chk) d≡Syn)

{-
 M.⟦ Δ ⟧ᵃ (ys , ρ̅)
      (All.map (λ {B = x} B⊆ {x = x₁} x∈ → Ds⊆ (B⊆ x∈)) Δ⊆Ds)
      (Syntax.BiTyped.Raw.Term.Raw Id D 0) (⊢⇔ Syn A) Γ t
-}

uniqᵐ-⇒
  : (Δ : TExps Ξ) {(xs , ρ) (xs′ , ρ′): ∃Sub⊆ Ξ} {Δ⊆ : Cover xs Δ} {Δ⊆′ : Cover xs′ Δ}
  → (xs , ρ) ≤ (xs′ , ρ′)
  → {Γ : Cxt 0}
  → {t : R.⟦ Δ ⟧ᵃ Raw (length Γ)} → ∀ {B C}
  → M.⟦ Δ ⟧ᵃ (xs  , ρ)  Δ⊆  Raw (_⊢_⇒ B) Γ t
  → M.⟦ Δ ⟧ᵃ (xs′ , ρ′) Δ⊆′ Raw (_⊢_⇒ C) Γ t
  → B ≡ C
uniqᵐ-⇒ []    _  ⊢t ⊢t′ =
  uniq-⇒ ⊢t ⊢t′
uniqᵐ-⇒ (A ∷ Δ) {xs , ρ} {xs′ , ρ′} {A⊆ ∷ Δ⊆} {A⊆′ ∷ Δ⊆′} p@(≤-con xs⊆xs′ ρ≤ρ′) {Γ} {t} ⊢t ⊢t′ =
  uniqᵐ-⇒ Δ {_} {_} {_} {Δ⊆′} p ⊢t
    $ subst (λ A → M.⟦ Δ ⟧ᵃ (xs′ , ρ′) Δ⊆′ Raw (_⊢_⇒ _) (A ∷ Γ) t)
      (ρ=σ→subρ=subσ A ρ′ ρ A⊆′ A⊆ (sym ∘ helper)) ⊢t′
    where
      open ≡-Reasoning
      helper : ∀ {x} (x∈ : x #∈ vars A) → ρ (A⊆ x∈) ≡ ρ′ (A⊆′ x∈)
      helper x∈ = begin
        ρ  (A⊆ x∈)
          ≡⟨ ρ≤ρ′ (A⊆ x∈) ⟩
        ρ′  (xs⊆xs′ (A⊆ x∈))
          ≡⟨ cong ρ′ (#∈-uniq _ _) ⟩
        ρ′ (A⊆′ x∈)
          ∎
