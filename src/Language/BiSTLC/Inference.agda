open import Prelude

module Language.STLC.Abstract.Inference where

open import Language.STLC.Abstract.Term as DB
-- open import ShadowingMembership

infix   5  ƛ_⇒_ _⇒ _⇐_
infixl  7  _·_
infix   9  `_

data Tm⁺ (Γ : Ty → Type) : Ty → Type
data Tm⁻ (Γ : Ty → Type) : Ty → Type

private
  variable
    A B C : Ty

data Tm⁺ Γ where
  ⊢`
    : Γ A
    → Tm⁺ Γ A
  _·_ 
    : Tm⁺ Γ (A ⇒ B) 
    → Tm⁻ Γ A
      ------------
    → Tm⁺ Γ B
  ⊢⇐ 
    : (A : Ty)
    → Tm⁻ Γ A
      -------------
    → Tm⁺ Γ A

data Tm⁻ Γ where
  ⊢ƛ 
    : Tm⁻ (Γ ▷ A) B
    → Tm⁻ Γ (A ⇒ B)

  ⊢⇒
    : Tm⁺ Γ  A
    → A ≡ B
      -------------
    → Tm⁻ Γ B
-- private
--   variable
--     x     : Id
--     Γ     : Cxt
--     A B   : Type

-- data Term⁺ : Set
-- data Term⁻ : Set

-- data Term⁺ where
--   `_                       : Id → Term⁺
--   _·_                      : Term⁺ → Term⁻ → Term⁺
--   proj₁_                   : Term⁺ → Term⁺
--   proj₂_                   : Term⁺ → Term⁺
--   _⇐_                      : Term⁻ → Type → Term⁺

-- data Term⁻ where
--   ƛ_⇒_                     : Id → Term⁻ → Term⁻
--   ⟨⟩                       : Term⁻
--   ⟨_,_⟩                    : Term⁻ → Term⁻ → Term⁻
--   _⇒                       : Term⁺ → Term⁻

-- ------------------------------------------------------------------------------
-- -- Bidirectional typing

-- data _⊢_⇒_ : (Γ : Cxt) → Term⁺ → Type → Set
-- data _⊢_⇐_ : (Γ : Cxt) → Term⁻ → Type → Set

-- data _⊢_⇒_ where
--   ⊢`
--     : Γ ∋ x ⦂ A
--       ---------------
--     → Γ ⊢ ` x ⇒ A

--   _·_ : ∀ {L M}
--     → Γ ⊢ L ⇒ A →̇ B
--     → Γ ⊢ M ⇐ A
--       ------------
--     → Γ ⊢ L · M ⇒ B

--   ⊢proj₁ : ∀ {M}
--     → Γ ⊢ M       ⇒ A ×̇ B
--     → Γ ⊢ proj₁ M ⇒ A

--   ⊢proj₂ : ∀ {M}
--     → Γ ⊢ M       ⇒ A ×̇ B
--     → Γ ⊢ proj₂ M ⇒ B

--   ⊢⇐ : ∀ {M}
--     → Γ ⊢ M     ⇐ A
--       -------------
--     → Γ ⊢ M ⇐ A ⇒ A

-- data _⊢_⇐_ where
--   ⊢ƛ : ∀ {N}
--     → Γ , x ⦂ A ⊢ N ⇐ B
--       -------------------------
--     → Γ         ⊢ ƛ x ⇒ N ⇐ A →̇ B

--   ⊢⟨⟩
--     : Γ ⊢ ⟨⟩ ⇐ ⊤̇

--   ⟨_,_⟩ : ∀ {N M}
--     → Γ ⊢ M         ⇐ A
--     → Γ ⊢ N         ⇐ B
--     → Γ ⊢ ⟨ M , N ⟩ ⇐ A ×̇ B

--   ⊢⇒ : ∀ {M}
--     → Γ ⊢ M ⇒ A
--     → A ≡ B
--       -------------
--     → Γ ⊢ (M ⇒) ⇐ B
    
-- ------------------------------------------------------------------------------
-- -- Erasure 

-- ∥_∥Cxt : Cxt → DB.Cxt
-- ∥ ∅         ∥Cxt =  DB.∅
-- ∥ Γ , x ⦂ A ∥Cxt =  ∥ Γ ∥Cxt DB., A

-- ∥_∥∋
--   : Γ ∋ x ⦂ A
--   → ∥ Γ ∥Cxt DB.∋ A
-- ∥ Z       ∥∋    =  DB.Z
-- ∥ S x≢ ∋x ∥∋    =  DB.S ∥ ∋x ∥∋

-- ∥_∥⁺ : ∀ {M}
--   → Γ           ⊢ M ⇒ A
--   → ∥ Γ ∥Cxt DB.⊢ A
-- ∥_∥⁻ : ∀ {M}
--   → Γ           ⊢ M ⇐ A
--   → ∥ Γ ∥Cxt DB.⊢ A 

-- ∥ ⊢` x      ∥⁺  = ` ∥ x ∥∋
-- ∥ M · N     ∥⁺  = ∥ M ∥⁺ · ∥ N ∥⁻ 
-- ∥ ⊢proj₁ M  ∥⁺  = proj₁ ∥ M ∥⁺
-- ∥ ⊢proj₂ M  ∥⁺  = proj₂ ∥ M ∥⁺
-- ∥ ⊢⇐ M      ∥⁺  = ∥ M ∥⁻

-- ∥ ⊢ƛ M      ∥⁻  = DB.ƛ ∥ M ∥⁻
-- ∥ ⊢⟨⟩       ∥⁻  = ⟨⟩
-- ∥ ⟨ M , N ⟩ ∥⁻  = ⟨ ∥ M ∥⁻ , ∥ N ∥⁻ ⟩
-- ∥ ⊢⇒ M refl ∥⁻  = ∥ M ∥⁺

-- ------------------------------------------------------------------------------
-- -- Uniqueness of synthesised type

-- uniq-⇒ : ∀ {M}
--   → Γ ⊢ M ⇒ A
--   → Γ ⊢ M ⇒ B
--   → A ≡ B
-- uniq-⇒ (⊢` x)       (⊢` y)        = uniq-∋ x y
-- uniq-⇒ (⊢M · _)     (⊢M′ · _)     = rng≡ (uniq-⇒ ⊢M ⊢M′)
-- uniq-⇒ (⊢⇐ x)       (⊢⇐ x₁)       = refl
-- uniq-⇒ (⊢proj₁ ⊢M)  (⊢proj₁ ⊢N)   = ×ₗ≡ (uniq-⇒ ⊢M ⊢N)
-- uniq-⇒ (⊢proj₂ ⊢M)  (⊢proj₂ ⊢N)   = ×ᵣ≡ (uniq-⇒ ⊢M ⊢N)

-- ------------------------------------------------------------------------------
-- -- Infectious failure

-- ¬arg : ∀ {L M}
--   → Γ ⊢ L ⇒ A →̇ B
--   → ¬ (Γ ⊢ M ⇐ A)
--     -------------------------
--   → ¬ (∃[ B′ ](Γ ⊢ L · M ⇒ B′))
-- ¬arg ⊢L ¬⊢M ( B′ , ⊢L′ · ⊢M′ ) rewrite dom≡ (uniq-⇒ ⊢L ⊢L′) = ¬⊢M ⊢M′

-- ¬switch : ∀ {M}
--   → Γ ⊢ M ⇒ A
--   → A ≢ B
--     --------------------
--   → ¬ (Γ ⊢ (M ⇒) ⇐ B)
-- ¬switch ⊢M A≢B (⊢⇒ ⊢M′ A′≡B) rewrite uniq-⇒ ⊢M ⊢M′ = A≢B A′≡B

-- ------------------------------------------------------------------------------
-- -- Synthesize and inherit types

-- synthesize
--   : (Γ : Cxt) (M : Term⁺)
--     --------------------------------
--   → Dec (∃[ A ] (Γ ⊢ M ⇒ A))
-- inherit
--   : (Γ : Cxt) (M : Term⁻) (A : Type)
--     ----------------------------------
--   → Dec (Γ ⊢ M ⇐ A)

-- synthesize Γ (` x)              with lookup Γ x
-- ... | no ¬∃        = no  λ{(A , ⊢` ∋x) → ¬∃ ( A , ∋x )}
-- ... | yes (A , ∋x) = yes (A , ⊢` ∋x)
-- synthesize Γ (L · M) with synthesize Γ L
-- ... | no  ¬∃                      =
--   no λ{ (_ , ⊢L  · _) → ¬∃ (_ , ⊢L ) }
-- ... | yes (ℕ̇     , ⊢L)            = no λ {(_ , ⊢L′ · _) → ℕ≢→ (uniq-⇒ ⊢L ⊢L′)}
-- ... | yes (⊤̇     , ⊢L)            = no λ {(_ , ⊢L′ · _) → ⊤≢→ (uniq-⇒ ⊢L ⊢L′) }
-- ... | yes (A ×̇ B , ⊢L)            = no λ {(_ , ⊢L′ · _) → ×≢→ (uniq-⇒ ⊢L ⊢L′) }
-- ... | yes (□ A   , ⊢L)            = no λ {(_ , ⊢L′ · _) → □≢→ (uniq-⇒ ⊢L ⊢L′) }
-- ... | yes (A →̇ B , ⊢L)            with inherit Γ M A
-- ...   | no ¬⊢M = no (¬arg ⊢L ¬⊢M)
-- ...   | yes ⊢M = yes (B , ⊢L · ⊢M)
-- synthesize Γ (proj₁ M)          with synthesize Γ M
-- ... | no ¬∃ =
--   no λ { (_ , ⊢proj₁ ⊢M) → ¬∃ (_ ×̇ _ , ⊢M) }
-- ... | yes (ℕ̇     , ⊢M)            = no λ {(_ , ⊢proj₁ ⊢M′) → ℕ≢× (uniq-⇒ ⊢M ⊢M′)}
-- ... | yes (⊤̇     , ⊢M)            = no λ {(_ , ⊢proj₁ ⊢M′) → ⊤≢× (uniq-⇒ ⊢M ⊢M′)}
-- ... | yes (A →̇ B , ⊢M)            = no λ {(_ , ⊢proj₁ ⊢M′) → ×≢→ (uniq-⇒ ⊢M′ ⊢M) }
-- ... | yes (□ A   , ⊢M)            = no λ {(_ , ⊢proj₁ ⊢M′) → □≢× (uniq-⇒ ⊢M ⊢M′) }
-- ... | yes (A ×̇ B , ⊢M)            = yes (A , ⊢proj₁ ⊢M)
-- synthesize Γ (proj₂ M)          with synthesize Γ M
-- ... | no ¬∃ =
--   no λ { (_ , ⊢proj₂ ⊢M) → ¬∃ (_ ×̇ _ , ⊢M) }
-- ... | yes (ℕ̇     , ⊢M)            = no λ {(_ , ⊢proj₂ ⊢M′) → ℕ≢× (uniq-⇒ ⊢M ⊢M′)}
-- ... | yes (⊤̇     , ⊢M)            = no λ {(_ , ⊢proj₂ ⊢M′) → ⊤≢× (uniq-⇒ ⊢M ⊢M′)}
-- ... | yes (A →̇ B , ⊢M)            = no λ {(_ , ⊢proj₂ ⊢M′) → ×≢→ (uniq-⇒ ⊢M′ ⊢M) }
-- ... | yes (□ A   , ⊢M)            = no λ {(_ , ⊢proj₂ ⊢M′) → □≢× (uniq-⇒ ⊢M ⊢M′) }
-- ... | yes (A ×̇ B , ⊢M)            = yes (B , ⊢proj₂ ⊢M)
-- synthesize Γ (M ⇐ A)            with inherit Γ M A
-- ... | no ¬⊢M = no λ { (_ , ⊢⇐ ⊢M) → ¬⊢M ⊢M }
-- ... | yes ⊢M = yes (A , ⊢⇐ ⊢M)

-- inherit Γ (ƛ x ⇒ M) (A →̇ B) with inherit (Γ , x ⦂ A) M B
-- ... | no ¬⊢M = no λ { (⊢ƛ M) → ¬⊢M M }
-- ... | yes ⊢M = yes (⊢ƛ ⊢M)
-- inherit Γ (ƛ x ⇒ M) ℕ̇       = no λ ()
-- inherit Γ (ƛ x ⇒ M) ⊤̇       = no λ ()
-- inherit Γ (ƛ x ⇒ M) (_ ×̇ _) = no λ ()
-- inherit Γ (ƛ x ⇒ M) (□ A)   = no λ ()
-- inherit Γ ⟨⟩ ⊤̇       = yes ⊢⟨⟩
-- inherit Γ ⟨⟩ ℕ̇       = no λ ()
-- inherit Γ ⟨⟩ (_ ×̇ _) = no λ ()
-- inherit Γ ⟨⟩ (_ →̇ _) = no λ () 
-- inherit Γ ⟨⟩ (□ _)   = no λ () 
-- inherit Γ ⟨ M , N ⟩ (A ×̇ B) with inherit Γ M A | inherit Γ N B
-- ... | no  ⊬M | _      = no λ { ⟨ ⊢M , _ ⟩ → ⊬M ⊢M }
-- ... | yes _  | no ⊬N  = no λ { ⟨ _ , ⊢N ⟩ → ⊬N ⊢N }
-- ... | yes ⊢M | yes ⊢N = yes ⟨ ⊢M , ⊢N ⟩
-- inherit Γ ⟨ _ , _ ⟩ ℕ̇       = no λ()
-- inherit Γ ⟨ _ , _ ⟩ ⊤̇       = no λ()
-- inherit Γ ⟨ _ , _ ⟩ (_ →̇ _) = no λ()
-- inherit Γ ⟨ _ , _ ⟩ (□ _)   = no λ()
-- inherit Γ (M ⇒) B       with synthesize Γ M
-- ... | no  ¬∃                =  no  (λ{ (⊢⇒ ⊢M _) → ¬∃ (_ , ⊢M) })
-- ... | yes (A , ⊢M) with A ≟Tp B
-- ...   | no  A≢B             =  no  (¬switch ⊢M A≢B)
-- ...   | yes A≡B             =  yes (⊢⇒ ⊢M A≡B)

-- ------------------------------------------------------------------------------
-- --

-- check-synthesized : (Γ : Cxt) (M : Term⁺) (A : Type) → Dec (Γ ⊢ M ⇒ A)
-- check-synthesized Γ M A with inherit Γ (M ⇒) A
-- ... | no ¬⊢M           = no λ ⊢M → ¬⊢M (⊢⇒ ⊢M refl)
-- ... | yes (⊢⇒ ⊢M refl) = yes ⊢M
