{-# OPTIONS --prop --rewriting --without-K #-}

module Tm where

open import Agda.Builtin.Equality renaming (_≡_ to _⇒_ ; refl to reduce)
open import Agda.Builtin.Equality.Rewrite

open import Data.Product
open import Util
open import SetoidEquality hiding (R ; S ; T)
open import Groupoid
open import Ty

record Tm (Γ : Con i) (A : Ty j Γ) : Set (i ⊔ j) where
  no-eta-equality
  field
    tm0 : (γ : ∣ Γ ∣) -> ∣ ∣ A ∣* γ ∣
    tm1 : ∀{γ γ'} -> (p : Hom Γ γ γ') -> IxHom A p (tm0 γ) (tm0 γ')

    tm-refl : ∀{γ} -> tm1 (R Γ γ) ≡ IxR A (tm0 γ)
    tm-trans : ∀{x y z} {p : Hom Γ x y} {q : Hom Γ y z}
             -> tm1 (T Γ p q) ≡ IxT A (tm1 p) (tm1 q)
open Tm public

postulate
  Tm≡ : {Γ : Con i} {A : Ty j Γ} {M N : Tm Γ A} {Γ' : Set k} {x y : Γ'} {p : Eq Γ' x y}
      -> HEq {Γ = Γ'} (λ _ -> Tm Γ A) p M N
     ⇒ ΣP (tm0 M ≡ tm0 N) λ eq1
       → Het {A = (γ : ∣ Γ ∣) -> ∣ ∣ A ∣* γ ∣}
             (λ t0 → ∀{γ γ'} -> (p : Hom Γ γ γ') -> IxHom A p (t0 γ) (t0 γ'))
             eq1 (tm1 M) (tm1 N)
{-# REWRITE Tm≡ #-}
