{-# OPTIONS --with-K --safe #-}

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

open import Data.Maybe                         public
  using (Maybe; nothing; just)

module N where
  open import Data.Nat as N       public
  open import Data.Nat.Properties public
open N public
  using (ℕ; zero; suc; _<′_; <′-base; <′-step; _⊔_; _+_; _∸_; less-than-or-equal; +-assoc; +-comm)
  renaming (_≤″_ to _≤_; _<″_ to _<_)

{-# DISPLAY N._≤′_ (suc n) m = n <′ m #-}

module F where
  open import Data.Fin          public
  open import Data.Fin.Literals public
open F public
  using (Fin; #_; zero; suc; fromℕ; punchOut; punchIn; _↑ˡ_; _↑ʳ_)

module L where
  open import Data.List                          public 
  open import Data.List.Properties               public

  open import Data.List.Relation.Unary.Any       public
    using (here; there)
  open import Data.List.Membership.Propositional public
    using (_∈_)
  open import Data.List.Membership.Propositional.Properties public
  open import Data.List.Relation.Unary.All       public
    using (All)
  open import Data.List.Relation.Binary.Subset.Propositional public
    using (_⊆_)
open L public using
  ( List; []; _∷_; length; _++_; zip
  ; _∈_; any; here; there; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺
  ; All; _⊆_)

module V where
  open import Data.Vec            public
  open import Data.Vec.Properties public
  open import Data.Vec.Relation.Unary.Any       public
    using (Any; here; there)
  open import Data.Vec.Membership.Propositional public
    using (_∈_)
open V public using
  (Vec; []; _∷_; map; insert; lookup; tabulate
  ; allFin; lookup∘tabulate)

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
  using (Decidable; Rel)
open import Relation.Binary.PropositionalEquality public
  using (_≡_; refl; sym; trans; cong; cong₂; subst; _≢_; module ≡-Reasoning)

module WF where
  open import Induction.WellFounded  public
open WF public
  hiding (module All)

open import Level                                 public
  using (Level; Lift; lift)
  renaming (zero to lzero; suc to lsuc; _⊔_ to lmax)

variable
  ℓ ℓ₀ ℓ₁ ℓ₂ ℓ′ : Level

private variable
  m n l : ℕ
  A : Set ℓ

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

infixl 4 _^_
_^_ : Set ℓ → ℕ → Set ℓ
X ^ n = Vec X n

Lift₀ : {ℓ : Level} → Set ℓ → Set ℓ
Lift₀ {ℓ} = Lift {ℓ} lzero -- Lift {ℓ} lzero

{-# DISPLAY Lift lzero A = Lift₀ A #-}
{-

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
-}
------------------------------------------------------------------------------
-- Properties of ≤
------------------------------------------------------------------------------

≤-step : {m n : ℕ} → m ≤ n → m ≤ suc n
≤-step {m} {n} (less-than-or-equal eq) = less-than-or-equal (begin
  m + (suc _)
    ≡⟨ N.+-suc m _ ⟩
  suc (m + _)
    ≡⟨ cong suc eq ⟩
  suc n
    ∎)
  where open ≡-Reasoning
    
≤-refl : ∀ {m} → m ≤ m
≤-refl = less-than-or-equal (N.+-identityʳ _)

-- Fin 
insert-mid : (m n : ℕ) → Fin (m + l) → Fin (m + n + l)
insert-mid m n i with F.splitAt m i
... | inl j = (j ↑ˡ _) ↑ˡ _
... | inr k = (m + n) ↑ʳ k


record DecEq {a} (A : Set a) : Set a where
  infix 4 _≟_
  field
    _≟_ : (x y : A) → Dec (x ≡ y)

open DecEq ⦃...⦄ public

instance
  EqNat : DecEq ℕ
  _≟_ ⦃ EqNat ⦄ = N._≟_

  EqFin : DecEq (Fin n)
  _≟_ ⦃ EqFin ⦄ = F._≟_
