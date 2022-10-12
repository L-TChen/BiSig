module Prelude where

open import Axiom.UniquenessOfIdentityProofs   public
open import Function                           public
  hiding (_∋_)
open import Data.Empty                         public
  using () renaming (⊥ to ⊥₀; ⊥-elim to ⊥-elim₀)
open import Data.Empty.Polymorphic             public
  using (⊥; ⊥-elim)
open import Data.Unit                          public
  using () renaming (⊤ to ⊤₀; tt to tt₀)
open import Data.Unit.Polymorphic              public
  using (⊤; tt)
open import Data.Nat                           public
  using (ℕ; zero; suc; _+_; _⊔_; less-than-or-equal)
  renaming (_≤″_ to _≤_)
import Data.Nat.Properties 
--  renaming (_≤′_ to _≤_; ≤′-refl to ≤-refl; ≤′-step to ≤-step)
module ℕₚ = Data.Nat.Properties

open import Data.Fin                           public
  using (Fin; #_; zero; suc; fromℕ)
open import Data.Fin.Literals                  public
open import Data.List                          public 
  using (List; length; map; _++_; zip)
  renaming ([] to ∅; _∷_ to _∙_)
open import Data.Maybe                         public
  using (Maybe; nothing; just)
open import Data.List.Membership.Propositional               public
open import Data.List.Relation.Unary.Any using (Any; here; there) public
open import Data.List.Relation.Unary.All public
  using (All)
open import Data.Vec                           public
  using (Vec; []; _∷_)
open import Data.String                        public
  using (String)
open import Data.Product                       public
  using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax; <_,_>)
open import Data.Sum                           public
  using (_⊎_; [_,_])
  renaming (inj₁ to inl; inj₂ to inr)

open import Relation.Nullary                      public
  using (Dec; yes; no; _because_; ¬_)
open import Relation.Binary                       public
  using (Decidable)
open import Relation.Binary.PropositionalEquality public
  using (_≡_; refl; sym; cong; cong₂; subst; _≢_; module ≡-Reasoning)

open import Level                                 public
  using (Level; Lift; lift)
  renaming (zero to lzero; suc to lsuc; _⊔_ to lmax)

variable
  ℓ ℓ₀ ℓ₁ ℓ₂ ℓ′ : Level

infixr -10 _⇒₁_ _⇒_
_⇒₁_ : {I : Set ℓ′}
  → (X : I → Set ℓ₁) (Y : I → Set ℓ₂) → Set _
X ⇒₁ Y = ∀ {i} → X i → Y i

_⇒_ : {I : Set ℓ₁} {J : Set ℓ₂}
  → (X : I → J → Set ℓ) (Y : I → J → Set ℓ′) → Set _
X ⇒ Y = ∀ {i j} → X i j → Y i j

data Mode : Set where
  Check Infer : Mode

_≟∈_ : {A : Set ℓ} {x y : A} {xs : List A} → (i : x ∈ xs) (j : y ∈ xs)
  → Dec ((x , i) ≡ (y , j))
here refl ≟∈ here refl = yes refl
there i   ≟∈ there j   with i ≟∈ j
... | no ¬p    = no λ where refl → ¬p refl
... | yes refl = yes refl
here _    ≟∈ there _   = no λ ()
there _   ≟∈ here  _   = no λ ()

_^_ : Set → ℕ → Set
X ^ zero  = ⊤₀
X ^ suc n = X × X ^ n

Lift₀ : {ℓ : Level} → Set ℓ → Set ℓ
Lift₀ {ℓ} = Lift {ℓ} lzero -- Lift {ℓ} lzero

{-# DISPLAY Lift lzero A = Lift₀ A #-}

private variable
  n : ℕ
  A : Set ℓ

strengthL : List (Fin (suc n)) → List (Fin n)
strengthL ∅            = ∅
strengthL (zero ∙ xs)  = strengthL xs
strengthL (suc x ∙ xs) = x ∙ strengthL xs

pred∈ : {y : Fin n} {xs : List (Fin (suc n))}
  → suc y ∈ xs → y ∈ strengthL xs
pred∈ {xs = _           } (here refl) = here refl
pred∈ {xs = (zero ∙ xs) } (there i)   = pred∈ i
pred∈ {xs = (suc x ∙ xs)} (there i)   = there (pred∈ i)

succ∈ : {y : Fin n} {xs : List (Fin (suc n))}
  → y ∈ strengthL xs → (suc y) ∈ xs
succ∈ {xs = zero  ∙ xs} i           = there (succ∈ i)
succ∈ {xs = suc x ∙ xs} (here refl) = here refl
succ∈ {xs = suc x ∙ xs} (there i)   = there (succ∈ i)

∈-length : {x : A} {xs : List A}
  → x ∈ xs → Fin (length xs)
∈-length (here _)  = zero
∈-length (there x) = suc (∈-length x)

update : (i : Fin n) (x : A) → Vec A n → Vec A n
update zero    y (x ∷ xs) = y ∷ xs
update (suc i) y (x ∷ xs) = x ∷ update i y xs

------------------------------------------------------------------------------
-- Properties of ≤
------------------------------------------------------------------------------

≤-step : {m n : ℕ} → m ≤ n → m ≤ suc n
≤-step {m} {n} (less-than-or-equal eq) = less-than-or-equal (begin
  m + (suc _)
    ≡⟨ ℕₚ.+-suc m _ ⟩
  suc (m + _)
    ≡⟨ cong suc eq ⟩
  suc n
    ∎)
  where open ≡-Reasoning
    
≤-refl : ∀ {m} → m ≤ m
≤-refl = less-than-or-equal (ℕₚ.+-identityʳ _)

-- m≤m+a+b : {m a b : ℕ}
--   → m ≤ m + a + b
-- m≤m+a+b {m} {a} {b} = less-than-or-equal {m} {m + a + b} {a + b} $ begin
--   m + (a + b)
--     ≡⟨ sym (ℕₚ.+-assoc m a b) ⟩
--   m + a + b
--   ∎ where open ≡-Reasoning
