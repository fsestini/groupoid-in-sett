{-# OPTIONS --prop --without-K --rewriting #-}

module Sigma where

open import Data.Product
open import Util
open import Equality
open import Groupoid
open import Substitution
open import Ty
open import Tm
open import Universes
open import CtxEquality
open import TyEquality

module _ (A : Ty j Γ) (B : Ty k (Γ ‣ A)) where

  private
    B' : ∀ γ → Ty k (∣ A ∣* γ)
    B' γ = record
      { ∣_∣* = λ a → ∣ B ∣* (_ , a)
      ; subst* = λ p → subst* B (R Γ _ , coe (λ z → Hom (∣ A ∣* _) z _) {!!} p)
      ; refl*0 = {!!}
      ; refl*1 = {!!}
      ; trans*0 = {!!}
      ; trans*1 = {!!}
      }

  Sigma : Ty _ Γ
  Sigma = record
    { ∣_∣* = λ γ → ∣ A ∣* γ ‣ B' γ
    ; subst* = λ {γ} {γ'} p → record
      { f0 = λ { (a , b) → f0 (subst* A p) a , f0 (subst* B (p , R (∣ A ∣* _) _)) b }
      ; f1 = λ { {a₀ , b₀} {a₁ , b₁} (q₀ , q₁) →
          let aux : HomEq (Γ ‣ A) {!!} {!!}
                          (p , R (∣ A ∣* _) (f0 (subst* A p) a₀))
                          (p , R (∣ A ∣* _) (f0 (subst* A p) a₁))
              aux = {!!}
              aux' : IxHom B {!!} b₀ b₁
              aux' = {!!}
              goal' = subst*-eq B aux aux'
              goal : IxHom (B' _) (f1 (subst* A p) q₀)
                           (f0 (subst* B (p , R (∣ A ∣* _) (f0 (subst* A p) a₀))) b₀)
                           (f0 (subst* B (p , R (∣ A ∣* _) (f0 (subst* A p) a₁))) b₁)
              goal = {!goal'!}
          in f1 (subst* A p) q₀ , goal
          }
      ; f-R = {!!}
      ; f-T = {!!}
      }
    ; refl*0 = λ x → sp (refl*0 A _) {!!}
    ; refl*1 = {!!}
    ; trans*0 = λ p q a → sp (trans*0 A _ _ _) {!!}
    ; trans*1 = {!!}
    }
