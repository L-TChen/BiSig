{-# OPTIONS --with-K --safe #-}

module Prelude where

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
  using (⊤; tt)

open import Data.Maybe                         public
  using (Maybe; nothing; just)

module N where
  open import Data.Nat as N       public
  open import Data.Nat.Properties public
open N public
  using (ℕ; zero; suc; _⊔_; _+_; _∸_; less-than-or-equal; +-assoc; +-comm)
  renaming (_≤″_ to _≤_; _≥″_ to _≥_; _<″_ to _<_)

module F where
  open import Data.Fin            public
  open import Data.Fin.Literals   public
  open import Data.Fin.Properties public
open F public
  using (Fin; #_; zero; suc; fromℕ; punchOut; punchIn; _↑ˡ_; _↑ʳ_
        ; punchIn-punchOut; punchOut-punchIn; punchInᵢ≢i)

module L where
  open import Data.List                          public
  open import Data.List.Properties               public

  open import Data.List.Relation.Unary.Any       public
    using (here; there; index)
  open import Data.List.Membership.Propositional public
    using (_∈_)
  open import Data.List.Membership.Propositional.Properties public
  open import Data.List.Relation.Unary.All       public
    using (All)
  open import Data.List.Relation.Binary.Subset.Propositional public
    using (_⊆_)
open L public using
  ( List; []; _∷_; length; _++_; zip
  ; any; here; there; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺
  ; All; _⊆_)
  renaming (_∈_ to infix 5 _∈_)

open import Data.Bool                          public
  using (Bool; true; false)

data And : List Bool → Bool → Set where
  nil :                       And []           true
  hd  : ∀ {bs}              → And (false ∷ bs) false
  tl  : ∀ {bs b} → And bs b → And (true  ∷ bs) b

module V where
  open import Data.Vec            public
  open import Data.Vec.Properties public
  open import Data.Vec.Relation.Unary.Any       public
    using (Any; here; there; index)
  open import Data.Vec.Membership.Propositional public
    using (_∈_)
open V public using
  (Vec; []; _∷_; toList; insert; lookup; tabulate
  ; allFin; tabulate∘lookup; lookup∘tabulate; tabulate-cong)

open import Data.String                        public
  using (String)
open import Data.Product                       public
  using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax; ∃₂; <_,_>; map₂; map₁)
open import Data.Product.Properties            public
open import Data.Sum                           public
  using (_⊎_; [_,_])
  renaming (inj₁ to inl; inj₂ to inr; map to ⊎-map)

open import Relation.Nullary                      public
  using (Dec; yes; no; _because_; ¬_)
open import Relation.Nullary.Decidable            public
  using (map′)
open import Relation.Binary                       public
  using (Decidable; Rel)
open import Relation.Binary.PropositionalEquality public
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; _≢_; module ≡-Reasoning)
  renaming (_≗_ to _≐_)

module WF where
  open import Induction.WellFounded  public
open WF public
  hiding (module All)

open import Level                                 public
  using (Level; Lift; lift)
  renaming (zero to lzero; suc to lsuc; _⊔_ to lmax)

open import Prelude.Equivalence                   public
open import Prelude.Logic                         public
open import Prelude.Category                      public

variable
  ℓ ℓ₀ ℓ₁ ℓ₂ ℓ′ : Level

private variable
  m n l : ℕ
  A B C : Set ℓ

data Mode : Set where
  Chk Inf : Mode

Chk≢Inf : Chk ≢ Inf
Chk≢Inf ()

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

------------------------------------------------------------------------------
-- Reverse append of Vector
------------------------------------------------------------------------------

_ʳ+_ : ℕ → ℕ → ℕ
zero  ʳ+ m = m
suc n ʳ+ m = n ʳ+ (suc m)

infixl 6 _ʳ+_
infixl 5 _ʳ++_

_ʳ++_ : Vec A n → Vec A m → Vec A (n ʳ+ m)
[]       ʳ++ ys = ys
(x ∷ xs) ʳ++ ys = xs ʳ++ (x ∷ ys)

splitAt : {A : Set}
  → (m : ℕ) (xs : Vec A (m ʳ+ n))
  → Σ[ ys ∈ Vec A m ] ∃[ zs ] xs ≡ ys ʳ++ zs
splitAt zero    xs = [] , xs , refl
splitAt (suc m) xs with splitAt m xs
splitAt (suc m) .(ys ʳ++ (z ∷ zs)) | ys , z ∷ zs , refl = z ∷ ys , zs , refl

ʳ++-≡ : {A : Set}
  → (xs xs′ : Vec A n) {ys ys′ : Vec A m}
  → xs ʳ++ ys ≡ xs′ ʳ++ ys′
  → xs ≡ xs′ × ys ≡ ys′
ʳ++-≡ []       []         {ys} {ys′} p = refl , p
ʳ++-≡ (x ∷ xs) (x′ ∷ xs′) {ys} {ys′} eq with ʳ++-≡ xs xs′ {x ∷ ys} {x′ ∷ ys′} eq
... | refl , refl = refl , refl

[xs]≢[] : {A : Set}
  → (xs : List A) {x : A}
  → xs L.++ L.[ x ] ≢ []
[xs]≢[] []       ()
[xs]≢[] (x ∷ xs) ()

∷-injectivity-⇔ : {A : Set ℓ} (t u : A) (ts us : Vec A n)
  → ((t V.∷ ts) ≡ (u ∷ us)) ⇔ ((t ≡ u) × (ts ≡ us))
∷-injectivity-⇔ t u ts us = record { to = V.∷-injective ; from = λ (t=u , ts=us) → cong₂ _∷_ t=u ts=us }
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

------------------------------------------------------------------------------
-- n ≤′ m is k + n ≡ m, i.e. n ≤ m with the LHS of the identity reversed.
------------------------------------------------------------------------------
record _≤′_ (m n : ℕ) : Set where
  constructor less-than-or-equal′
  field
    {k}   : ℕ
    proof : k + m ≡ n

infix 4 _≤′_ _<′_ _≥′_ _>′_

_<′_ : Rel ℕ _
m <′ n = suc m ≤′ n

_≥′_ : Rel ℕ _
m ≥′ n = n ≤′ m

_>′_ : Rel ℕ _
m >′ n = n <′ m

≤⇒≤′ : {n m : ℕ} → n ≤ m → n ≤′ m
≤⇒≤′ {n} {m} (less-than-or-equal p) = less-than-or-equal′ $ begin
  _ + n
    ≡⟨ +-comm _ n ⟩
  n + _
    ≡⟨ p ⟩
  m ∎
  where open ≡-Reasoning

------------------------------------------------------------------------------
-- Well-Foundedness of _<_ and _<′_
------------------------------------------------------------------------------
<′-accs : (y x : ℕ) → x <′ y → Acc _<′_ x
<′-accs zero    x (less-than-or-equal′ {k} p) = ⊥-elim₀ (N.m+1+n≢0 _ p)
<′-accs (suc y) y (less-than-or-equal′ {zero}  refl) = acc (<′-accs y)
<′-accs (suc y) x (less-than-or-equal′ {suc k} refl) = <′-accs y x (less-than-or-equal′ {k = k} refl)

<′-wf : WellFounded _<′_
<′-wf = acc ∘ <′-accs

<-wf : WellFounded _<_
<-wf = Subrelation.wellFounded  ≤⇒≤′ <′-wf

-- Fin
insert-mid : (m n : ℕ) → Fin (m + l) → Fin (m + n + l)
insert-mid m n i with F.splitAt m i
... | inl j = (j ↑ˡ _) ↑ˡ _
... | inr k = (m + n) ↑ʳ k

------------------------------------------------------------------------------
-- Type classes
------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Decidable Equality

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
