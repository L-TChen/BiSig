open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Raw.Term {SD : S.Desc} (Id : Set) (D : B.Desc {SD}) where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp)

open import Syntax.BiTyped.Raw.Functor {SD} Id

private variable
  n m k : ℕ
  mod : Mode

infix 4 _⦂_

data Raw (m : ℕ) : Mode → Set where
  `_  : (x : Id)                       → Raw m Infer
  _⦂_ : (t : Raw m Check) (A : TExp m) → Raw m Infer
  _↑  : (t : Raw m Infer)              → Raw m Check
  op  : (⟦ D ⟧ Raw m) mod              → Raw m mod

Raw⇇ Raw⇉ : ℕ → Set
Raw⇇ m = Raw m Check
Raw⇉ m = Raw m Infer

mutual
  twkˡ : m ≤ n → Raw m mod → Raw n mod
  twkˡ le (` x)   = ` x
  twkˡ le (t ⦂ A) = twkˡ le t ⦂ wk≤ˡ le A 
  twkˡ le (t ↑)   = twkˡ le t ↑
  twkˡ le (op (D , i , refl , ts)) = op (D , i , refl , twkˡⁿ le ts)

  twkˡⁿ : {D : B.ArgsD k}
    → m ≤ n → ⟦ D ⟧ᵃˢ Raw m → ⟦ D ⟧ᵃˢ Raw n
  twkˡⁿ {D = ∅}     le (lift _) = _
  twkˡⁿ {D = A ∙ D} le (t , ts) = twkˡᵃ le t , twkˡⁿ le ts

  twkˡᵃ : {D : List (TExp k)}
    → m ≤ n → ⟦ D ⟧ᵃ Raw m mod → ⟦ D ⟧ᵃ Raw n mod
  twkˡᵃ {D = ∅}     le t       = twkˡ le t
  twkˡᵃ {D = A ∙ D} le (x , t) = x , twkˡᵃ le t

mutual
  twkᵐ : (m n {l} : ℕ) → Raw (m + l) mod → Raw (m + n + l) mod
  twkᵐ m n (` x)   = ` x
  twkᵐ m n (t ⦂ A) = twkᵐ m n t ⦂ wkᵐ m n A
  twkᵐ m n (t ↑)   = twkᵐ m n t ↑
  twkᵐ m n (op (D , i , refl , ts)) =
    op (D , i , refl , twkᵐⁿ m n ts)

  twkᵐⁿ : {D : B.ArgsD k}
    → (m n {l} : ℕ) 
    → ⟦ D ⟧ᵃˢ Raw (m + l) → ⟦ D ⟧ᵃˢ Raw (m + n + l)
  twkᵐⁿ {D = ∅}     m n (lift _) = _
  twkᵐⁿ {D = A ∙ D} m n (t , ts) = twkᵐᵃ m n t , twkᵐⁿ m n ts

  twkᵐᵃ : {D : List (TExp k)}
    → (m n {l} : ℕ)
    → ⟦ D ⟧ᵃ Raw (m + l) mod → ⟦ D ⟧ᵃ Raw (m + n + l) mod
  twkᵐᵃ {D = ∅}     m n t       = twkᵐ m n t
  twkᵐᵃ {D = A ∙ D} m n (x , t) = x , twkᵐᵃ m n t
