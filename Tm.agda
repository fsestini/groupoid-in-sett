{-# OPTIONS --prop --rewriting --without-K #-}

module Tm where

open import Agda.Builtin.Equality renaming (_≡_ to _⇒_ ; refl to reduce)
open import Agda.Builtin.Equality.Rewrite

open import Data.Product
open import Util
open import Equality
open import Groupoid
open import Ty

record Tm (Γ : Con i) (A : Ty j Γ) : Set (i ⊔ j) where
  field
    tm0 : (γ : ∣ Γ ∣) -> ∣ ∣ A ∣* γ ∣
    tm1 : ∀{γ γ'} -> (p : Hom Γ γ γ') -> IxHom A p (tm0 γ) (tm0 γ')

    tm-refl : ∀{γ} -> tm1 (R Γ γ) ≡ IxR A (tm0 γ)
    tm-trans : ∀{x y z} {p : Hom Γ x y} {q : Hom Γ y z}
             -> tm1 (T Γ p q) ≡ IxT A (tm1 p) (tm1 q)
open Tm public

postulate
  Tm≡ : {Γ : Con i} {A : Ty j Γ} {M N : Tm Γ A}
      -> M ≡ N
     ⇒ ΣP (tm0 M ≡ tm0 N) λ eq1
       → HEq {I = (γ : ∣ Γ ∣) -> ∣ ∣ A ∣* γ ∣}
             (λ t0 → ∀{γ γ'} -> (p : Hom Γ γ γ') -> IxHom A p (t0 γ) (t0 γ'))
             eq1 (tm1 M) (tm1 N)

  Tm≡' : {I : Set k} {Γ : I -> Con i} {A : (x : I) -> Ty j (Γ x)}
         {i0 i1 : I} {p : i0 ≡ i1} {M : Tm (Γ i0) (A i0)} {N : Tm (Γ i1) (A i1)}
       -> HEq (λ x → Tm (Γ x) (A x)) p M N
        ⇒ ΣP (HEq (λ w → (γ : ∣ Γ w ∣) → ∣ ∣ A w ∣* γ ∣) p (tm0 M) (tm0 N)) λ eq1
            → HEq {I = Σ I (λ w → (γ : ∣ Γ w ∣) → ∣ ∣ A w ∣* γ ∣)}
                  (λ w → ∀{γ γ'} -> (p : Hom (Γ (proj₁ w)) γ γ') -> IxHom (A (proj₁ w)) p (proj₂ w γ) (proj₂ w γ'))
                  (sp p (λ {a} {a'} r → eq1 r)) (tm1 M) (tm1 N)

{-# REWRITE Tm≡ Tm≡' #-}
