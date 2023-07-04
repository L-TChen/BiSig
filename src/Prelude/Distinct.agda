{-# OPTIONS --safe #-}

module Prelude.Distinct where

open import Data.List.Fresh as F public
  using ([] ; cons; fresh; _∷#_)
  renaming (List# to List##)

module A where
  open import Data.List.Fresh.Relation.Unary.All   public
  open import Data.List.Fresh.Relation.Unary.Any   public
    hiding (map)
open A public
  using ([]; _∷_; here; there)

open import Data.Unit
  using (⊤; tt) 
open import Data.Nat
  using (ℕ)
open import Data.Fin
  using (Fin)
open import Data.Empty
open import Data.Product
open import Data.Sum

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Prelude.Level
open import Prelude.DecEq

List# : Set → Set
List# A = List## A _≢_

Fins# : ℕ → Set
Fins# n = List# (Fin n)

private variable
  A        : Set
  x y      : A
  xs ys zs : List# A 

infix 5 _#_

_#_ : A → List# A → Set _
_#_ x xs = fresh _ _≢_ x xs

_##_ : List# A → List# A → Set
[]        ## ys = ⊤
(x ∷# xs) ## ys = x # ys × (xs ## ys)

All : (P : A → Set) → List# A → Set _
All P xs = A.All P xs

Map : List# A → Set → Set
Map xs V = All (λ _ → V) xs

infix 5 _#∈_ _#∉_ _#⊆_

_#∈_ _#∉_ : A → List# A → Set _
x #∈ xs = A.Any (x ≡_) xs

x #∉ xs = ¬ x #∈ xs 

_#⊆_ : (xs y : List# A) → Set _
xs #⊆ ys = ∀ {x} → x #∈ xs → x #∈ ys

≡→⊆ : xs ≡ ys → xs #⊆ ys
≡→⊆ refl x = x

[]⊆xs : [] #⊆ xs
[]⊆xs ()
#⊆-refl : xs #⊆ xs
#⊆-refl x = x

⊆-trans : xs #⊆ ys → ys #⊆ zs → xs #⊆ zs
⊆-trans xs⊆ys ys⊆zs x∈ = ys⊆zs (xs⊆ys x∈)

∈→¬fresh : (xs : List# A) → x #∈ xs → x # xs → ⊥
∈→¬fresh (cons y xs _) (here eq)  (x≠y , _)  = x≠y eq
∈→¬fresh (cons y xs _) (there x∈) (_ , x#xs) = ∈→¬fresh xs x∈ x#xs

#∈-uniq : (x∈ x∈′ : x #∈ xs) → x∈ ≡ x∈′
#∈-uniq (here refl) (here refl) = refl
#∈-uniq {xs = cons x xs x#xs} (here refl) (there x∈′) =
  ⊥-elim (∈→¬fresh _ x∈′ x#xs) 
#∈-uniq {xs = cons x xs x#xs} (there x∈)  (here refl) =
  ⊥-elim (∈→¬fresh _ x∈  x#xs)
#∈-uniq (there x∈) (there x∈′)  = cong there (#∈-uniq x∈ x∈′)

-- union
--   : (xs : List# A) (ys : List# A) → xs ## ys → List# A
-- fresh-union
--   : x # xs → (xs#ys : xs ## ys) → x # ys
--   → x # union xs ys xs#ys
--   
-- union []               ys tt             = ys
-- union (cons x xs x#xs) ys (x#ys , xs#ys) =
--   cons x (union xs ys xs#ys) (fresh-union x#xs xs#ys x#ys)
-- 
-- fresh-union {xs = []}      _            _           x#ys = x#ys
-- fresh-union {xs = y ∷# xs} (x≠y , x#xs) (_ , xs#xs) x#ys =
--   x≠y , fresh-union x#xs xs#xs x#ys
--   
-- union⁺ˡ : (xs#ys : xs ## ys) → xs ⊆ union xs ys xs#ys
-- union⁺ˡ xs#ys       (here eq)  = here eq
-- union⁺ˡ (_ , xs#ys) (there x∈) = there (union⁺ˡ xs#ys x∈)
-- 
-- union⁺ʳ : (xs#ys : xs ## ys) → ys ⊆ union xs ys xs#ys
-- union⁺ʳ {xs = []}     xs#ys       x∈ = x∈
-- union⁺ʳ {xs = _ ∷# _} (_ , xs#ys) x∈ = there (union⁺ʳ xs#ys x∈)

module Decidable {A : Set} ⦃ _ : DecEq A ⦄ where
  fresh? : (x : A) (xs : List# A) → x # xs ⊎ x #∈ xs
  fresh? x [] = inj₁ _
  fresh? x (cons y xs y#xs) with x ≟ y
  ... | yes eq = inj₂ (here eq)
  ... | no neq with fresh? x xs
  ... | inj₁ x#xs = inj₁ (neq , x#xs)
  ... | inj₂ x∈xs = inj₂ (there x∈xs)

  infixr 8 _∪_

  _∪_     : (xs ys : List# A) → List# A
  fresh-∪ : x # xs → x # ys → x # (xs ∪ ys)

  []           ∪ ys = ys
  cons x xs px ∪ ys with fresh? x ys
  ... | inj₁ x#ys = cons x (xs ∪ ys) (fresh-∪ px x#ys)
  ... | inj₂ x∈ys = xs ∪ ys

  fresh-∪ {x} {[]}             {ys} _   pys = pys
  fresh-∪ {x} {cons y xs y#xs} {ys} (px , x#xs) x#ys with fresh? y ys
  ... | inj₁ y#ys = px , fresh-∪ x#xs x#ys
  ... | inj₂ y∈ys = fresh-∪ x#xs x#ys

  ∈-∪⁻
    : ∀ {x : A} xs {ys : List# A}
    → x #∈ xs ∪ ys
    → x #∈ xs ⊎ x #∈ ys
  ∈-∪⁻ []               x∈ = inj₂ x∈
  ∈-∪⁻ (cons y xs x#xs) {ys} x∈ with fresh? y ys
  ... | inj₂ ¬pys with ∈-∪⁻ xs x∈
  ... | inj₁ x∈xs = inj₁ (there x∈xs)
  ... | inj₂ x∈ys = inj₂ x∈ys
  ∈-∪⁻ (cons y xs x#xs) (here eq)  | inj₁ pys = inj₁ (here eq)
  ∈-∪⁻ (cons y xs x#xs) (there x∈) | inj₁ pys with ∈-∪⁻ xs x∈
  ... | inj₁ x∈xs = inj₁ (there x∈xs)
  ... | inj₂ x∈ys = inj₂ x∈ys
  
  ∪⁺ʳ
    : (xs {ys} : List# A)
    → ys #⊆ xs ∪ ys
  ∪⁺ʳ []                   x∈ = x∈
  ∪⁺ʳ (cons x xs pxs) {ys} x∈ with fresh? x ys
  ... | inj₁ x#ys = there (∪⁺ʳ xs x∈)
  ... | inj₂ _    = ∪⁺ʳ xs x∈
  
  ∪⁺ˡ 
    : {xs ys : List# A}
    → xs #⊆ xs ∪ ys
  ∪⁺ˡ {y ∷# xs} {ys} x∈ with fresh? y ys
  ∪⁺ˡ {y ∷# xs} (here refl) | inj₂ y∈ys =
    ∪⁺ʳ xs y∈ys
  ∪⁺ˡ (there x∈) | inj₂ _  = ∪⁺ˡ x∈
  ∪⁺ˡ (here eq)  | inj₁ _ = here eq
  ∪⁺ˡ (there x∈) | inj₁ _ = there (∪⁺ˡ x∈)

  ∪-⊆⁺ : xs #⊆ zs → ys #⊆ zs → xs ∪ ys #⊆ zs
  ∪-⊆⁺  {xs} xs⊆ ys⊆ x∈ with ∈-∪⁻ xs x∈
  ... | inj₁ ∈xs = xs⊆ ∈xs
  ... | inj₂ ∈ys = ys⊆ ∈ys

  ∪-⊆⁻ˡ : xs ∪ ys #⊆ zs → xs #⊆ zs
  ∪-⊆⁻ˡ  xs∪ys⊆zs x∈xs = xs∪ys⊆zs (∪⁺ˡ x∈xs)

  ∪-⊆⁻ʳ : ∀ xs → xs ∪ ys #⊆ zs → ys #⊆ zs
  ∪-⊆⁻ʳ  xs xs∪ys⊆zs x∈xs = xs∪ys⊆zs (∪⁺ʳ xs x∈xs)

  ∪-monotoneʳ : ∀ xs → ys #⊆ zs → xs ∪ ys #⊆ xs ∪ zs
  ∪-monotoneʳ xs ys⊆zs x∈ with ∈-∪⁻ xs x∈
  ... | inj₁ x∈xs = ∪⁺ˡ x∈xs 
  ... | inj₂ x∈ys = ∪⁺ʳ xs (ys⊆zs x∈ys)
open Decidable public

-- module Decidable {A : Set} ⦃ _ : DecEq A ⦄ where
--   allFresh? : (xs : List# A) (ys : List# A) → Dec (xs ## ys)
--   allFresh? []        _  = yes tt
--   allFresh? (x ∷# xs) ys with allFresh? xs ys
--   ... | no ¬p = no λ where
--     (_ , p) → ¬p p
--   ... | yes p with fresh? x ys
--   ... | no ¬q = no λ where
--     (q , _) → ¬q q
--   ... | yes q = yes (q , p)

--   ¬fresh→∈ : {xs : List# A} → ¬ x # xs → x ∈ xs 
--   ¬fresh→∈ {_} {[]}             ¬x#xs = ⊥-elim (¬x#xs (lift tt))
--   ¬fresh→∈ {x} {cons y xs y#xs} ¬x#xs with x ≟ y
--   ... | yes eq = here eq
--   ... | no ¬eq = there (¬fresh→∈ (λ x#xs → ¬x#xs (¬eq , x#xs)))
  
--   find? : (xs : List# A) → (x : A) → Dec (x ∈ xs)
--   find? []        _ = no λ ()
--   find? (y ∷# xs) x with x ≟ y
--   ... | yes eq = yes (here eq)
--   ... | no neq with find? xs x
--   ... | yes x∈ = yes (there x∈)
--   ... | no x∉  = no λ where
--     (here eq)  → neq eq
--     (there x∈) → x∉ x∈

--   infixr 8 _∪_
