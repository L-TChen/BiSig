open import Prelude

open import Generic.Signature

module Generic.Term (Ds : ConDs) where

open import Generic.Term.Base Ds public
open import Generic.Term.Fold Ds public
open import Generic.Term.Renaming     Ds public
open import Generic.Term.Substitution Ds public
