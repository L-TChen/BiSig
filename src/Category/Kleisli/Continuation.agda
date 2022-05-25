open import Prelude

module Category.Kleisli.Continuation where

open import Category.Kleisli
open Monad
open MonadLaw

record Cont (V : Type) (X : Type) : Type where
  constructor cont
  field
    runCont : (X → V) → V
open Cont public

instance
  ContMonad : {V : Type} → Monad (Cont V)
  return ContMonad x   .runCont ρ = ρ x
  _=<<_  ContMonad f k .runCont ρ = k .runCont λ x → f x .runCont ρ
  unit-left   (law ContMonad) x _ .runCont ρ = x .runCont ρ
  unit-right  (law ContMonad) {f = f} x _ .runCont ρ = f x .runCont ρ
  associative (law ContMonad) f g k i .runCont ρ =
    k .runCont (λ x → f x .runCont (λ y → g y .runCont ρ))
