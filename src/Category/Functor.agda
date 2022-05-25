open import Prelude

module Category.Functor where

private
  variable
    X Y Z : Type

record RawFunctor (F : Type → Type) : Type₁ where
  field
    fmap : {X Y : Type}
      → (X → Y) → F X → F Y

record FunctorLaw (F : Type → Type) (raw : RawFunctor F) : Type₁ where
  open RawFunctor raw
  field
    fmap-id : (x : F X)
      → fmap {X} {X} id x ≡ x
    fmap-comp : (f : X → Y) (g : Y → Z)
      → (x : F X)
      → fmap (g ∘ f) x ≡ fmap g (fmap f x)

record Functor (F : Type → Type) : Type₁ where
  field
    raw : RawFunctor F
    law : FunctorLaw F raw
  open RawFunctor raw public
  open FunctorLaw law public

record RawPtFunctor (F : Type → Type) : Type₁ where
  field
    ⦃ rawFunc ⦄ : RawFunctor F
    pure        : X → F X

  open RawFunctor rawFunc public
