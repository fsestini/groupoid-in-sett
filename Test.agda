{-# OPTIONS --prop --without-K --rewriting #-}

module Test where

open import Agda.Builtin.Equality renaming (_≡_ to _⇒_ ; refl to reduce)
open import Agda.Builtin.Equality.Rewrite

open import Util
open import Equality

record Test (i : Level) : Set (lsuc i) where
  field
    ∣_∣ : Set i
    Hom : ∣_∣ -> ∣_∣ -> Set i
open Test

postulate
  Test≡ : {i : Level} (A B : Test i)
        → (A ≡ B)
        ⇒ ΣP (∣ A ∣ ≡ ∣ B ∣) λ eq
        → HEq (λ X → X -> X -> Set i) eq (Hom A) (Hom B)

{-# REWRITE Test≡ #-}

module _ {i : Level} (A B : Test i) where

  uh : A ≡ B
  uh = sp {!!} {!!}
