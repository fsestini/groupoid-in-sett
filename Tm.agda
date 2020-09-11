{-# OPTIONS --prop --rewriting --without-K #-}

module Tm where

open import Agda.Builtin.Equality renaming (_≡_ to _⇒_ ; refl to reduce)
open import Agda.Builtin.Equality.Rewrite

open import Lib
open import SetoidEquality
open import Groupoid
open import Ty

record Tm (Γ : Con i) (A : Ty j Γ) : Set (i ⊔ j) where
  no-eta-equality
  field
    tm0 : (γ : ∣ Γ ∣) -> ∣ ∣ A ∣* γ ∣
    tm1 : ∀{γ γ'} -> (p : Hom Γ γ γ') -> IxHom A p (tm0 γ) (tm0 γ')

    tm-refl : ∀{γ} -> tm1 (R Γ γ) ≡ IxR A (tm0 γ)
    -- tm-trans : ∀{x y z} {p : Hom Γ x y} {q : Hom Γ y z}
    --          -> tm1 (T Γ p q) ≡ IxT A (tm1 p) (tm1 q)
open Tm public

postulate
  Tm≡ : {Γ : Con i} {A : Ty j Γ} {M N : Tm Γ A}
      -> Eq (Tm Γ A) M N
     ⇒ Σp (tm0 M ≡ tm0 N) λ eq1
       → HEq {I = (γ : ∣ Γ ∣) -> ∣ ∣ A ∣* γ ∣}
             (λ t0 → ∀{γ γ'} -> (p : Hom Γ γ γ') -> IxHom A p (t0 γ) (t0 γ'))
             eq1 (tm1 M) (tm1 N)
{-# REWRITE Tm≡ #-}
