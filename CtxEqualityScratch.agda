{-# OPTIONS --prop --rewriting --without-K #-}

module CtxEqualityScratch where

open import Data.Product
open import Util
open import Equality
open import Groupoid
open import Substitution
open import Ty
open import Tm
open import Universes

open import CtxEquality


module _ (Γ : Con i) {ρ₀ ρ₁ : Δ ⟶ Γ} (p : Tm Δ (El-set ((Γ ~) ρ₀ ρ₁))) where

  id1~~ : Tm Δ (El-prop ((Γ ~~) ρ₀ ρ₁ (id-fun Δ) (id-fun Δ) (R~ (id-fun Δ)) (T~ ρ₀ ρ₁ ρ₁ p (R~ ρ₁)) p))
  id1~~ = record
    { tm0 = λ δ →
        lift (snd' (HomEq-eq12 Γ (f-R ρ₀) (f-R ρ₁))
             (snd' (HomEq-eq34 Γ (id1 Γ) (refl (tm0 p δ)))
             (HomEq-R Γ (tm0 p δ))))
    ; tm1 = λ _ → lift tt
    ; tm-refl = tt
    ; tm-trans = tt
    }

  id2~~ : Tm Δ (El-prop ((Γ ~~) ρ₀ ρ₁ (id-fun Δ) (id-fun Δ) (R~ (id-fun Δ)) (T~ ρ₀ ρ₀ ρ₁ (R~ ρ₀) p) p))
  id2~~ = record
    { tm0 = λ δ → let tr = hom-tr Γ in
        lift (snd' (HomEq-eq12 Γ (f-R ρ₀) (f-R ρ₁))
             (snd' (HomEq-eq34 Γ (id2 Γ) (refl (tm0 p _)))
             (tr (cong (T Γ (S Γ _)) (id1 Γ))
             (tr (cong (λ z → T Γ z _) (S-id Γ)) (id2 Γ)))))
    ; tm1 = λ _ → lift tt
    ; tm-refl = tt
    ; tm-trans = tt
    }
