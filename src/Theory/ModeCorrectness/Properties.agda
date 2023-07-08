import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

import Theory.ModeCorrectness.Description as MC

module Theory.ModeCorrectness.Properties {SD : S.Desc}
  (D : B.Desc SD) (mc : MC.ModeCorrect SD D) where

open import Prelude

import Data.List.Relation.Unary.All as All

open import Syntax.Simple  SD
open import Syntax.Context SD

import      Syntax.Typed.Raw.Functor       SD as R
open import Syntax.BiTyped.Functor         SD
import      Theory.ModeCorrectness.Functor SD as M

open import Theory.Erasure

open import Syntax.Typed.Raw.Term (erase D)
open import Syntax.BiTyped.Term          D

open import Theory.ModeCorrectness.UniqueSynthesised D mc

open MC SD
open B  SD
open ≡-Reasoning

private variable
  d     : Mode
  Ξ n   : ℕ
  xs ys : Fins# Ξ
  Γ     : Cxt 0
  t u   : Raw n

module _ {ρ σ : ∃Sub⊆ Ξ} (ρ≤σ : ρ ≤ σ) where
  ρ≤σ→⊢tᵃ
    : (Δ : TExps Ξ) {Δ⊆xs : Cover _ Δ} {Δ⊆xs′ : Cover _ Δ}
    → {Γ : Cxt 0} {t : R.⟦ Δ ⟧ᵃ Raw (length Γ)} {B : Ty}
    → M.⟦ Δ ⟧ᵃ σ Δ⊆xs  Raw (_⊢_[ d ] B) Γ t
    → M.⟦ Δ ⟧ᵃ ρ Δ⊆xs′ Raw (_⊢_[ d ] B) Γ t
  ρ≤σ→⊢tᵃ []                ⊢t = ⊢t
  ρ≤σ→⊢tᵃ (A ∷ Δ) {A⊆ ∷ Δ⊆} {A⊆′ ∷ Δ⊆′} ⊢t
    rewrite sub⊆-cong (ρ .proj₂) (σ .proj₂) A A⊆′ A⊆ (λ x∈ → begin
        ρ .proj₂ _
          ≡⟨ ρ≤σ .consistency _  ⟩
        σ .proj₂ _
          ≡⟨ cong (σ .proj₂) (#∈-uniq _ _) ⟩
        σ .proj₂ _
          ∎) = ρ≤σ→⊢tᵃ Δ ⊢t

module _ {ρ σ : ∃Sub⊆ Ξ} (ρ≤σ : ρ ≤ σ) where
  ρ≤σ→⊢tᵃ′
    : (Δ : TExps Ξ) {Δ⊆xs : Cover _ Δ} {Δ⊆xs′ : Cover _ Δ}
    → {Γ : Cxt 0} {t : R.⟦ Δ ⟧ᵃ Raw (length Γ)} {B : Ty}
    → M.⟦ Δ ⟧ᵃ ρ Δ⊆xs′ Raw (_⊢_[ d ] B) Γ t
    → M.⟦ Δ ⟧ᵃ σ Δ⊆xs  Raw (_⊢_[ d ] B) Γ t
  ρ≤σ→⊢tᵃ′ []      ⊢t = ⊢t
  ρ≤σ→⊢tᵃ′ (A ∷ Δ) {A⊆xs ∷ ⊆xs} {A⊆xs′ ∷ ⊆xs′} ⊢t
    rewrite sub⊆-cong (ρ .proj₂) (σ .proj₂) A A⊆xs′ A⊆xs λ x∈ →
      begin
        ρ .proj₂ (A⊆xs′ x∈)
          ≡⟨ ρ≤σ .consistency (A⊆xs′ x∈)  ⟩
        σ .proj₂ _
          ≡⟨ cong (σ .proj₂) (#∈-uniq _ _) ⟩
        σ .proj₂ (A⊆xs x∈)
          ∎ = ρ≤σ→⊢tᵃ′ Δ ⊢t

  ρ≤σ→⊢tⁿ′
    : (Ds : ArgsD Ξ) (ys : Fins# Ξ) (mc : ModeCorrectᵃˢ ys Ds)
    → {Ds⊆  : ys ∪ known Ds #⊆ _}
    → {Ds⊆′ : ys ∪ known Ds #⊆ _}
    → {Γ : Cxt 0} {ts : R.⟦ eraseᵃˢ Ds ⟧ᵃˢ Raw (length Γ)}
    → M.⟦ Ds ⟧ᵃˢ ρ ys Ds⊆  mc Raw _⊢_[_]_ Γ ts
    → M.⟦ Ds ⟧ᵃˢ σ ys Ds⊆′ mc Raw _⊢_[_]_ Γ ts
  ρ≤σ→⊢tⁿ′ []                   _  _     _   = tt
  ρ≤σ→⊢tⁿ′ (Δ ⊢[ Chk ] Aₙ ∷ Ds) ys (A⊆ ∷ Δ⊆ , mc) {Ds⊆} {Ds⊆′} (⊢t , ⊢ts)
    rewrite sub⊆-cong (ρ .proj₂) (σ .proj₂) Aₙ (Ds⊆ ∘ A⊆) (Ds⊆′ ∘ A⊆) λ x∈ →
      begin
        ρ .proj₂ _
          ≡⟨ ρ≤σ .consistency _  ⟩
        σ .proj₂ _
          ≡⟨ cong (σ .proj₂) (#∈-uniq _ _) ⟩
        σ .proj₂ _
          ∎ = ρ≤σ→⊢tᵃ′ Δ ⊢t , ρ≤σ→⊢tⁿ′ _ _ _ ⊢ts
  ρ≤σ→⊢tⁿ′ (Δ ⊢[ Syn ] Aₙ ∷ Ds) ys (Δ⊆ , mc) {Ds⊆} {Ds⊂′} (⊢t , ⊢ts)
    rewrite sub⊆-cong (ρ .proj₂) (σ .proj₂) Aₙ (λ x → Ds⊆ (∪⁺ʳ ys (∪⁺ˡ x))) (λ x → Ds⊂′ (∪⁺ʳ ys (∪⁺ˡ x))) λ x∈ →

      begin
        ρ .proj₂ _
          ≡⟨ ρ≤σ .consistency _  ⟩
        σ .proj₂ _
          ≡⟨ cong (σ .proj₂) (#∈-uniq _ _) ⟩
        σ .proj₂ _
          ∎ = ρ≤σ→⊢tᵃ′ Δ ⊢t , ρ≤σ→⊢tⁿ′ _ _ _ ⊢ts

------------------------------------------------------------------------
-- Typing derivations with substitution
-- to derivatios with partial substitution

module _ {σ : TSub Ξ 0} where
  ⊢ᵃ→Sub⊆⊢ᵃ
    : ∀ Δ {Γ} A {t}
    → {Δ⊆ : Cover (enumerate Ξ) Δ}
    → ⟦ Δ ⟧ᵃ Raw (_⊢_[ d ] (A ⟨ σ ⟩)) σ Γ t
    → M.⟦ Δ ⟧ᵃ (_ , Sub⇒Sub⊆ σ) Δ⊆ Raw (_⊢_[ d ] (sub⊆ (Sub⇒Sub⊆ σ) A λ {x} _ → ⊆enum x)) Γ t
  ⊢ᵃ→Sub⊆⊢ᵃ []      {Γ} B ⊢t rewrite sub⊆=sub σ B = ⊢t
  ⊢ᵃ→Sub⊆⊢ᵃ (A ∷ Δ) {Γ} B {t} {A⊆ ∷ Δ⊆} ⊢t
    rewrite sub⊆=sub σ A rewrite sub⊆-⊆-irrelevant (Sub⇒Sub⊆ σ) A  (λ {x = x₁} _ → ⊆enum x₁) A⊆ =
    ⊢ᵃ→Sub⊆⊢ᵃ Δ B ⊢t

  ⊢ᵃˢ→Sub⊆⊢ᵃˢ
    : {Ds : ArgsD Ξ}
    → {mc : ModeCorrectᵃˢ ys Ds}
    → {Γ : Cxt 0} {ts : R.⟦ eraseᵃˢ Ds ⟧ᵃˢ Raw (length Γ)}
    → ⟦ Ds ⟧ᵃˢ Raw _⊢_[_]_ σ Γ ts
    → M.⟦ Ds ⟧ᵃˢ (_ , Sub⇒Sub⊆ σ) ys (λ {x} _ → ⊆enum x) mc Raw _⊢_[_]_ Γ ts
  ⊢ᵃˢ→Sub⊆⊢ᵃˢ {Ds = []}                                  _          = tt
  ⊢ᵃˢ→Sub⊆⊢ᵃˢ {Ds = Δ B.⊢[ Chk ] Aₙ ∷ Ds} {A⊆ ∷ Δ⊆ , mc} {ts = t , ts} (⊢t , ⊢ts) =
     ⊢ᵃ→Sub⊆⊢ᵃ Δ Aₙ ⊢t  , ⊢ᵃˢ→Sub⊆⊢ᵃˢ ⊢ts
  ⊢ᵃˢ→Sub⊆⊢ᵃˢ {Ds = Δ ⊢[ Syn ] Aₙ ∷ Ds}   {Δ⊆ , mc}      (⊢t , ⊢ts) =
    ⊢ᵃ→Sub⊆⊢ᵃ Δ Aₙ ⊢t , ⊢ᵃˢ→Sub⊆⊢ᵃˢ ⊢ts

-----------------------------------------------------------------------
-- Typing derivations with partial substitution
-- to derivatios with substitution

module _ {ρ : Sub⊆ Ξ xs} where
  Sub⊆⊢ᵃ→⊢ᵃ
    : ∀ Δ {Γ} A {t}
    → (Δ⊆ : Cover xs Δ)
    → (A⊆ : vars A #⊆ xs)
    → (⊆xs : ∀ x → x #∈ xs)
    → M.⟦ Δ ⟧ᵃ (_ , ρ) Δ⊆ Raw (_⊢_[ d ] (sub⊆ ρ A A⊆)) Γ t
    → ⟦ Δ ⟧ᵃ Raw (_⊢_[ d ] (sub (ρ ∘ ⊆xs) A)) (ρ ∘ ⊆xs) Γ t
  Sub⊆⊢ᵃ→⊢ᵃ []      B _         B⊆ ⊆xs ⊢t rewrite sub⊆=sub′ ρ ⊆xs B B⊆ = ⊢t
  Sub⊆⊢ᵃ→⊢ᵃ (A ∷ Δ) B (A⊆ ∷ Δ⊆) B⊆ ⊆xs ⊢t rewrite sub⊆=sub′ ρ ⊆xs A A⊆ =
    Sub⊆⊢ᵃ→⊢ᵃ Δ B Δ⊆ B⊆ ⊆xs ⊢t

  Sub⊆⊢ᵃˢ→⊢ᵃˢ
    : {Ds : ArgsD Ξ} {ys : Fins# Ξ}
    → {⊆xs : (x : Fin Ξ) → x #∈ xs} {ys∪Ds⊆ : ys ∪ known Ds #⊆ xs} {mc : ModeCorrectᵃˢ ys Ds}
    → {Γ : Cxt 0} {ts : R.⟦ eraseᵃˢ Ds ⟧ᵃˢ Raw (length Γ)}
    → M.⟦ Ds ⟧ᵃˢ (_ , ρ) ys ys∪Ds⊆ mc Raw _⊢_[_]_ Γ ts
    → ⟦ Ds ⟧ᵃˢ Raw _⊢_[_]_ (Sub⊆⇒Sub ρ ⊆xs) Γ ts
  Sub⊆⊢ᵃˢ→⊢ᵃˢ {[]}                              tt = tt
  Sub⊆⊢ᵃˢ→⊢ᵃˢ {Δ ⊢[ Chk ] Aₙ ∷ Ds} {ys} {⊆xs} {ys∪Ds⊆} {A⊆ ∷ Ds⊆ , mc} {Γ} {t , ts} (⊢t , ⊢ts) =
     Sub⊆⊢ᵃ→⊢ᵃ Δ Aₙ _ _ _ ⊢t  , Sub⊆⊢ᵃˢ→⊢ᵃˢ ⊢ts
  Sub⊆⊢ᵃˢ→⊢ᵃˢ {Δ ⊢[ Syn ] Aₙ ∷ Ds} {ys} {⊆xs} {ys∪Ds⊆} {mc} {Γ} {t , ts} (⊢t , ⊢ts) =
    Sub⊆⊢ᵃ→⊢ᵃ Δ Aₙ _ _ _ ⊢t , Sub⊆⊢ᵃˢ→⊢ᵃˢ ⊢ts
