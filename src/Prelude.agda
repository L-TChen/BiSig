{-# OPTIONS --safe #-}

module Prelude where

open import Agda.Builtin.FromNat               public

open import Axiom.UniquenessOfIdentityProofs   public
open import Function                           public
  hiding (_∋_; id; Equivalence; _⇔_)
open import Data.Empty                         public
  using () renaming (⊥ to ⊥₀; ⊥-elim to ⊥-elim₀)
open import Data.Empty.Polymorphic             public
  using (⊥; ⊥-elim)

open import Data.Unit                          public
  using () renaming (⊤ to ⊤₀; tt to tt₀)
open import Data.Unit.Polymorphic              public
  using (⊤)

open import Data.Maybe                         public
  using (Maybe; just; nothing)
module N where
  open import Data.Nat            public
  open import Data.Nat.Literals   public
  open import Data.Nat.Properties public
open N public
  using (ℕ; zero; suc; _+_; _∸_; less-than-or-equal; +-assoc; +-comm)

module F where
  open import Data.Fin            public
  open import Data.Fin.Literals   public
  open import Data.Fin.Properties public
open F public
  using (Fin; #_; zero; suc; fromℕ; _↑ˡ_; _↑ʳ_; punchIn; punchOut)

module L where
  open import Data.List                          public
  open import Data.List.Properties               public

  open import Data.List.Relation.Unary.Any       public
    using (Any; here; there; index)
  open import Data.List.Relation.Unary.Any.Properties public
    hiding (map-id; map-∘)
  open import Data.List.Membership.Propositional public
    using (_∈_)
  open import Data.List.Membership.Propositional.Properties public
  module A where
    open import Data.List.Relation.Unary.All            public
    open import Data.List.Relation.Unary.All.Properties public
  open A using (All; []; _∷_) public
  
  open import Data.List.Relation.Binary.Subset.Propositional public
    using (_⊆_)
open L public using
  ( List; []; _∷_; length; _++_; zip
  ; any; here; there; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺
  )
  renaming (_∈_ to infix 5 _∈_)

module V where
  open import Data.Vec            public
  open import Data.Vec.Properties public
--  open import Data.Vec.Relation.Unary.Any       public
--    using (Any; here; there; index)
--  open import Data.Vec.Relation.Unary.All      public
--    using (All; []; _∷_)
  open import Data.Vec.Membership.Propositional public
open V public using
  (Vec; []; _∷_)

open import Data.String                        public
  using (String)
open import Data.Product                       public
  using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax; ∃₂; <_,_>; map₂; map₁; curry; uncurry)
open import Data.Product.Properties            public
  hiding (≡-dec)
open import Data.Sum                           public
  using (_⊎_; [_,_])
  renaming (inj₁ to inl; inj₂ to inr; map to ⊎-map)

open import Relation.Nullary                      public
  using (Dec; yes; no; _because_; ¬_; ¬?)
open import Relation.Nullary.Decidable            public
  using (map′)
open import Relation.Binary                       public
  using (Decidable; Rel; IsEquivalence)
open import Relation.Binary.PropositionalEquality public
  using (_≡_; _≗_; refl; sym; trans; cong; cong₂; subst; subst₂; _≢_; isPropositional; module ≡-Reasoning)
  renaming (isEquivalence to ≡-isEquivalence)

module WF where
  open import Induction.WellFounded  public
open WF public
  hiding (module All)

open import Prelude.Level                         public
open import Prelude.Equivalence                   public
open import Prelude.Logic                         public
open import Prelude.Category                      public
open import Prelude.Distinct                      public

private variable
  m n l : ℕ
  A B C : Set ℓ
  
pattern tt = lift tt₀

data Mode : Set where
  Chk Syn : Mode

infixl 4 _^_
_^_ : Set ℓ → ℕ → Set ℓ
X ^ n = Vec X n

Fins : ℕ → Set
Fins = List ∘ Fin

Lift₀ : {ℓ : Level} → Set ℓ → Set ℓ
Lift₀ {ℓ} = Lift {ℓ} 0ℓ

{-# DISPLAY Lift lzero A = Lift₀ A #-}

------------------------------------------------------------------------------
-- Properties of _≗_

≗-isEquivalence : IsEquivalence (_≗_ {A = A} {B = B})
≗-isEquivalence = record
  { refl  = λ {f} x → refl
  ; sym   = λ {f} {g} eq → sym ∘ eq 
  ; trans = λ {f} {g} {h} f=g g=h x → trans (f=g x) (g=h x)
  }

------------------------------------------------------------------------------
-- Type classes
------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- Decidable Equality

open import Prelude.DecEq public

instance
  EqNat : DecEq ℕ
  _≟_ ⦃ EqNat ⦄ = N._≟_

  EqFin : DecEq (Fin n)
  _≟_ ⦃ EqFin ⦄ = F._≟_

instance
  NumNat : Number ℕ
  NumNat = N.number

  NumFin : {n : ℕ} → Number (Fin n)
  NumFin {n} = F.number n
