import Syntax.Simple.Signature  as S
import Syntax.BiTyped.Signature as B

import Theory.ModeCorrectness.Signature as MC

module Theory.ModeCorrectness.Synthesis
  {SD : S.SigD} (D : B.SigD SD) (mc : MC.ModeCorrect SD D) where

open import Prelude

import Data.List.Relation.Unary.All as All

open import Syntax.Simple  SD
open import Syntax.Context SD

open import Syntax.BiTyped.Functor     SD
import      Syntax.BiTyped.Pre.Functor SD as P
import      Syntax.Typed.Raw.Functor   SD as R

open import Theory.Erasure

open import Syntax.BiTyped.Term          D
open import Syntax.BiTyped.Pre.Term      D
open import Syntax.Typed.Raw.Term (erase D)

open import Theory.ModeCorrectness.Functor   SD as M

open import Theory.ModeCorrectness.UniqueSynthesised D mc
open import Theory.ModeCorrectness.Properties        D mc

open MC SD
open B  SD
open ≡-Reasoning

private variable
  Ξ     : ℕ
  xs ys : Fins# Ξ

module _ where mutual
  synthesise
    : (Γ : Cxt 0) {r : Raw (length Γ)}
    → Pre Syn r → Dec (∃[ A ] Γ ⊢ r ⇒ A)

  check
    : (Γ : Cxt 0) {r : Raw (length Γ)}
    → Pre Chk r → (A : Ty) → Dec (Γ ⊢ r ⇐ A)

  synthesise Γ (` x) = yes (L.lookup Γ x , var (L.∈-lookup x) (L.index-∈-lookup Γ x))

  synthesise Γ (A ∋ t) with check Γ t A
  ... | no  ⊬t = no λ where (A , ._ ∋ ⊢t) → ⊬t ⊢t
  ... | yes ⊢t = yes (A , _ ∋ ⊢t)

  synthesise Γ (op ts) with synthesiseᶜ (SigD.ar D _) (mc _) Γ ts
  ... | no  ⊬t       = no λ where (A , op ⊢t) → ⊬t (A , ⊢t)
  ... | yes (A , ⊢t) = yes (A , op ⊢t)

  check Γ (t ↑) A with synthesise Γ t
  ... | no ⊬t = no (why t ⊬t)
    where
      why : {r : Raw (length Γ)} → Pre Syn r → ¬ (∃[ B ] Γ ⊢ r ⇒ B) → ¬ Γ ⊢ r ⇐ A
      why _                ⊬t (t ↑ _)          = ⊬t (_ , t)
      why (op (d≡Syn , _)) ⊬t (op (d≡Chk , _)) = Chk≢Syn (trans (sym d≡Chk) d≡Syn)
  ... | yes (B , ⊢t) with A ≟ B
  ... | no ¬A=B = no (¬switch ⊢t ¬A=B)
  ... | yes A=B = yes (⊢t ↑ A=B)

  check Γ (op ts@(d≡Chk , _)) A with checkᶜ (SigD.ar D _) (mc _) Γ ts A
  ... | no ⊬t = no λ where
    (op (d≡Syn , _) ↑ _) → Chk≢Syn (trans (sym d≡Chk) d≡Syn)
    (op ⊢t)              → ⊬t ⊢t
  ... | yes ⊢t = yes (op ⊢t)

  checkᶜ
    : (D : OpD) → ModeCorrectᶜ D
    → (Γ : Cxt 0) {rs : R.⟦ eraseᶜ D ⟧ᶜ Raw (length Γ)}
    → P.⟦ D ⟧ᶜ Raw Pre Chk rs → (A : Ty) → Dec (⟦ D ⟧ᶜ Raw _⊢_[_]_ Γ rs Chk A)
  checkᶜ (ι Chk A₀ Ds) (⊆A∪Ds , SDs) Γ (refl , ts) A with cmp A₀ A
  ... | noₘ   A₀≉A = no λ where
    (_ , σ , eq , ⊢t) → A₀≉A (_ , Sub⇒Sub⊆ σ) ((λ {x} x∈ → ⊆enum x) , (begin
      sub⊆ _ A₀ _
        ≡⟨ Sub⇒Sub⊆-= σ A₀ ⟩
      sub σ A₀
        ≡⟨ eq ⟩
      A
        ∎))
  ... | yesₘ (_ , ρ) A₀≈A@(min-con (A₀⊆ , A₀=A) minρ) with synthesiseⁿ Ds SDs Γ ts (_ , ρ) A₀⊆
  ... | noₘ ¬Pσ   = let ⊆A₀ = domain-cmp A₀ A _ ρ A₀≈A in no λ where
    (_ , σ , eq , ⊢ts) → ¬Pσ (_ , Sub⇒Sub⊆ σ) (ext-con (≤-con (λ {x} _ → ⊆enum x) (λ {x} x∈ → begin
      ρ x∈
        ≡⟨ cong ρ (#∈-uniq _ _) ⟩
      ρ _
        ≡⟨ sub-σ=sub⊆-ρ→σ=ρ ρ σ A₀ A₀⊆ (trans A₀=A (sym eq)) (⊆A₀ x∈) ⟩
      σ x
        ∎)) ((λ {x} _ → ⊆enum x) , ⊢ᵃˢ→Sub⊆⊢ᵃˢ ⊢ts))
  ... | yesₘ (_ , ρ̅) (min-con (ext-con (≤-con ρ⊆ρ̅ ρ≤ρ̅) (A₀∪Ds⊆ , ⊢ts)) minρ̅) =
    yes (refl , Sub⊆⇒Sub ρ̅ (A₀∪Ds⊆ ∘ ⊆A∪Ds) ,
      (begin _ ≡⟨ Sub⊆⇒Sub-≡ ρ̅ (A₀∪Ds⊆ ∘ ⊆A∪Ds) A₀ ⟩
        sub⊆ ρ̅ A₀ (λ {x} _ → A₀∪Ds⊆ (⊆A∪Ds x))
         ≡⟨ sym (ρ=σ→subρ=subσ A₀ ρ ρ̅ _ _ λ x∈ → trans (ρ≤ρ̅ (A₀⊆ x∈)) (cong ρ̅ (#∈-uniq _ _))) ⟩
        sub⊆ ρ A₀ A₀⊆
           ≡⟨ A₀=A ⟩
        A
         ∎) , Sub⊆⊢ᵃˢ→⊢ᵃˢ ⊢ts)

  synthesiseᶜ
    : (D : OpD) → ModeCorrectᶜ D
    → (Γ : Cxt 0) {rs : R.⟦ eraseᶜ D ⟧ᶜ Raw (length Γ)}
    → P.⟦ D ⟧ᶜ Raw Pre Syn rs → Dec (∃[ A ] ⟦ D ⟧ᶜ Raw _⊢_[_]_ Γ rs Syn A)
  synthesiseᶜ (ι Syn A Ds) (Ds⊆Ξ , SDs , A⊆Ds) Γ (refl , ts)
    with synthesiseⁿ Ds SDs Γ ts empty (λ ())
  ... | noₘ   ¬Pσ = no λ where
    (A , _ , σ , refl , ⊢ts) → ¬Pσ (_ , Sub⇒Sub⊆ σ) (ext-con ∅≤ρ ((λ {x} x∈ → ⊆enum x) , ⊢ᵃˢ→Sub⊆⊢ᵃˢ ⊢ts))
  ... | yesₘ ρ (min-con (ext-con []≤ρ (Ds⊆ , ⊢ts)) minρ) =
    let ρ′ = Sub⊆⇒Sub (ρ .proj₂) (Ds⊆ ∘ Ds⊆Ξ) in
    yes (A ⟨ ρ′ ⟩ , refl , ρ′ , refl , Sub⊆⊢ᵃˢ→⊢ᵃˢ ⊢ts)

  synthesiseⁿ
    : (Ds : ArgsD Ξ) (mc : ModeCorrectᵃˢ ys Ds)
    → (Γ : Cxt 0) {rs : R.⟦ eraseᵃˢ Ds ⟧ᵃˢ Raw (length Γ)}
    → P.⟦ Ds ⟧ᵃˢ Raw Pre rs
    → ((xs , ρ) : ∃Sub⊆ Ξ) (ys⊆ : ys #⊆ xs)
    → MinDec (Ext (_ , ρ) λ ρ̅ →
        Σ[ Ds⊆ ∈ ys ∪ known Ds #⊆ _ ] M.⟦ Ds ⟧ᵃˢ ρ̅ ys Ds⊆ mc Raw _⊢_[_]_ Γ rs)
  synthesiseⁿ []       _        _ _        ρ ys⊆ = yesₘ ρ (Pρ→MinExtP (ys⊆ ∘ ∪-⊆⁺ #⊆-refl []⊆xs , _))

  synthesiseⁿ {ys = ys} (Δ ⊢[ Syn ] Aₙ ∷ Ds) (Δ⊆Ds , mc) Γ {r , rs} (t , ts) ρ ys⊆ with synthesiseⁿ Ds mc Γ ts ρ ys⊆

  ... | noₘ ¬∃σ = noₘ λ where
    σ (ext-con ρ≤σ (Ds⊆ , ⊢t , ⊢ts)) → ¬∃σ σ (ext-con ρ≤σ (Ds⊆ ∘ ∪-monotoneʳ ys (∪⁺ʳ (vars Aₙ)) , ⊢ts))

  ... | yesₘ (ys′ , ρ̅) (min-con (ext-con ρ≤ρ̅ (Ds⊆ , ⊢ts)) minρ̅)
    with synthesiseᵃ Δ (_ , ρ̅) (All.map (λ {B} B⊆ {x} x∈ → Ds⊆ (B⊆ x∈)) Δ⊆Ds) Γ t
  ... | no  ¬⊢t = noₘ λ where
    (zs , σ) (ext-con ρ≤σ (Ds⊆′ , ⊢t , ⊢ts)) →
      let ρ̅≤σ = minρ̅ (_ , σ) (ext-con ρ≤σ (Ds⊆′ ∘ ∪-monotoneʳ ys (∪⁺ʳ (vars Aₙ)) , ⊢ts)) in
      ¬⊢t (sub⊆ σ Aₙ (Ds⊆′ ∘ λ x∈ → ∪⁺ʳ ys (∪⁺ˡ x∈)) , ρ≤σ→⊢tᵃ ρ̅≤σ Δ ⊢t)

  ... | yes (A , ⊢t) with acmp Aₙ A (_ , ρ̅)

  ... | noₘ ¬Aₙ≈A  = noₘ λ where
    (zs , σ) (ext-con ρ≤σ (Ds⊆′ , ⊢t′ , ⊢ts′)) →
      let ρ̅≤σ = minρ̅ (_ , σ) (ext-con ρ≤σ (Ds⊆′ ∘ ∪-monotoneʳ ys (∪⁺ʳ (vars Aₙ)) , ⊢ts′))
      in ¬Aₙ≈A (_ , σ) (ext-con (minρ̅ (_ , σ) record
        { ext     = ≤-trans ρ≤ρ̅ ρ̅≤σ
        ; witness = (Ds⊆′ ∘ ∪-monotoneʳ ys (∪⁺ʳ (vars Aₙ))) , ⊢ts′
        }) (_ , sym (uniqᵐ-⇒ Δ ρ̅≤σ ⊢t ⊢t′)))

  ... | yesₘ (zs , σ) (min-con (ext-con ρ̅≤σ@(≤-con ys⊆zs _) (Aₙ⊆ , refl)) minσ) = yesₘ (_ , σ) (record
    { proof      = record
      { ext     = ≤-trans ρ≤ρ̅ ρ̅≤σ
      ; witness =  ∪-⊆⁺ {xs = ys} ((ys⊆zs ∘ ρ≤ρ̅ .domain-ext) ∘ ys⊆) (∪-⊆⁺ Aₙ⊆ (ys⊆zs ∘ Ds⊆ ∘ ∪⁺ʳ ys))  , subst (λ A →
        M.⟦ Δ ⟧ᵃ (_ , σ) (L.A.map (λ {A} A⊆ {x} x∈ → _ ) Δ⊆Ds) Raw (_⊢_[ Syn ] A) Γ r) (sub⊆-⊆-irrelevant σ Aₙ _ _) (ρ≤σ→⊢tᵃ′ ρ̅≤σ Δ ⊢t) ,
        ρ≤σ→⊢tⁿ′ ρ̅≤σ  Ds ys mc ⊢ts
      }
    ; minimality = λ where
      (zs′ , γ) (ext-con ρ≤γ (Ds⊆′ , ⊢t′ , ⊢ts′)) →
        let ρ̅≤γ = minρ̅ (_ , γ) (ext-con ρ≤γ (Ds⊆′ ∘ ∪-monotoneʳ ys (∪⁺ʳ (vars Aₙ)) , ⊢ts′)) in
        minσ (_ , γ) record
        { ext     = ρ̅≤γ
        ; witness = Ds⊆′ ∘ ∪⁺ʳ ys ∘ ∪⁺ˡ , sym (uniqᵐ-⇒ Δ ρ̅≤γ ⊢t ⊢t′)
        }
    })

  synthesiseⁿ (Δ ⊢[ Chk ] Aₙ ∷ Ds) (A⊆Ds ∷ Δ⊆Ds , mc) Γ {r , rs} (t , ts) ρ ys⊆ with synthesiseⁿ Ds mc Γ ts ρ ys⊆

  ... | noₘ ¬∃σ = noₘ λ where
    σ (ext-con ρ≤σ (Ds⊆ , ⊢t , ⊢ts)) → ¬∃σ σ (ext-con ρ≤σ (Ds⊆ , ⊢ts))

  ... | yesₘ (xs , ρ̅) (min-con (ext-con ρ≤ρ̅ (Ds⊆ , ⊢ts)) minρ̅)
    with checkᵃ Δ (xs , ρ̅) (L.A.map (λ {B} B⊆ {x} x∈ → Ds⊆ (B⊆ x∈)) Δ⊆Ds) Γ t (sub⊆ ρ̅ Aₙ (Ds⊆ ∘ A⊆Ds))

  ... | no  ¬⊢t = noₘ λ where
    (zs , σ) (ext-con ρ̅≤σ (Ds⊆′ , ⊢t′ , ⊢ts′)) →
      let ρ̅≤σ = minρ̅ (_ , σ) (ext-con ρ̅≤σ (Ds⊆′ , ⊢ts′))
          eq : sub⊆ σ Aₙ (λ x → Ds⊆′ (A⊆Ds x)) ≡ sub⊆ ρ̅ Aₙ (λ x → Ds⊆ (A⊆Ds x))
          eq = begin
            sub⊆ σ Aₙ (λ x → Ds⊆′ (A⊆Ds x))
              ≡⟨ ρ=σ→subρ=subσ Aₙ σ ρ̅ (Ds⊆′ ∘ A⊆Ds) (Ds⊆ ∘ A⊆Ds)
                (λ x∈ → begin
                  σ (Ds⊆′ (A⊆Ds x∈))
                    ≡⟨ cong σ (#∈-uniq _ _) ⟩
                  σ _
                    ≡⟨ sym (ρ̅≤σ .consistency (Ds⊆ (A⊆Ds x∈))) ⟩
                  ρ̅ (Ds⊆ (A⊆Ds x∈))
                    ∎) ⟩
            sub⊆ ρ̅ Aₙ _
              ≡⟨ sub⊆-⊆-irrelevant ρ̅ Aₙ _ _ ⟩
            sub⊆ ρ̅ Aₙ (λ x → Ds⊆ (A⊆Ds x))
              ∎
      in
      ¬⊢t (ρ≤σ→⊢tᵃ ρ̅≤σ Δ (subst (λ A → M.⟦ Δ ⟧ᵃ (_ , σ) _ Raw (_⊢_[ Chk ] A) Γ r) eq ⊢t′))

  ... | yes ⊢t = yesₘ (_ , ρ̅) (min-con (ext-con ρ≤ρ̅ (Ds⊆ , ⊢t , ⊢ts))
    λ σ (ext-con ρ≤σ (Ds⊆′ , ⊢t , ⊢ts)) → minρ̅ σ (ext-con ρ≤σ (Ds⊆′ , ⊢ts)))

  synthesiseᵃ
    : (Δ : TExps Ξ) ((xs , ρ) : ∃Sub⊆ Ξ) (Δ⊆ : Cover xs Δ)
    → (Γ : Cxt 0) {r : R.⟦ Δ ⟧ᵃ Raw (length Γ)}
    → P.⟦ Δ ⟧ᵃ Raw Pre Syn r
    → Dec (∃[ A ] M.⟦ Δ ⟧ᵃ (_ , ρ) Δ⊆ Raw (_⊢_⇒ A) Γ r)
  synthesiseᵃ []      (_ , ρ) Δ⊆        Γ t = synthesise Γ t
  synthesiseᵃ (A ∷ Δ) (_ , ρ) (A⊆ ∷ Δ⊆) Γ t =
    synthesiseᵃ Δ (_ , ρ) (Δ⊆) (sub⊆ ρ A (A⊆) ∷ Γ) t

  checkᵃ
    : (Δ : TExps Ξ) ((xs , ρ) : ∃Sub⊆ Ξ) (Δ⊆ : Cover xs Δ)
    → (Γ : Cxt 0) {r : R.⟦ Δ ⟧ᵃ Raw (length Γ)}
    → P.⟦ Δ ⟧ᵃ Raw Pre Chk r
    → (A : Ty) → Dec (M.⟦ Δ ⟧ᵃ (_ , ρ) Δ⊆ Raw (_⊢_⇐ A) Γ r)
  checkᵃ []      (_ , ρ) Δ⊆        Γ t A₀ = check Γ t A₀
  checkᵃ (A ∷ Δ) (_ , ρ) (A⊆ ∷ Δ⊆) Γ t A₀ =
    checkᵃ Δ (_ , ρ) Δ⊆ (sub⊆ ρ A A⊆ ∷ Γ) t A₀
