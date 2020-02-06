{-# OPTIONS --prop --rewriting --without-K --allow-unsolved-metas #-}

module TyEquality where

open import Data.Product
open import Util
open import Equality
open import Groupoid
open import Substitution
open import Ty
open import Tm
open import Universes
open import CtxEquality


module _ {Γ : Con i} {Δ : Con k} (A : Ty j Γ) (γ₀ γ₁ : Δ ⟶ Γ) where

  _~*' : Tm Δ (A [ γ₀ ]) -> Tm Δ (A [ γ₁ ]) -> Tm (Δ ‣ El-set ((Γ ~) γ₀ γ₁)) (Set-ty j)
  _~*' a₀ a₁ = record
    { tm0 = λ { (δ , p) → IxHom A p (tm0 a₀ δ) (tm0 a₁ δ) }
    ; tm1 = λ { {δ , p} {δ' , p'} (q , r) →
        let goal : Iso (IxHom A p (tm0 a₀ δ) (tm0 a₁ δ)) (IxHom A p' (tm0 a₀ δ') (tm0 a₁ δ'))
            goal = record
                   { iso1 = λ f → transp-IxHom A (unlift r) (IxT A (IxS A (tm1 a₀ q)) (IxT A f (tm1 a₁ q)))
                   ; iso2 = λ f → transp-IxHom A (hom-tr Γ (cong (λ z → T Γ z (T Γ p' _))
                                    (hom-sy Γ (SS-id Γ))) (HomEq-S Γ (unlift r)))
                                    (IxT A (tm1 a₀ q) (IxT A f (IxS A (tm1 a₁ q))))
                   ; prf1 = {!!} ; prf2 = {!!} }
        in goal }
    ; tm-refl = {!!}
    ; tm-trans = {!!}
    }

  _~* : Tm Δ (El-set ((Γ ~) γ₀ γ₁))
      -> Tm Δ (A [ γ₀ ]) -> Tm Δ (A [ γ₁ ]) -> Tm Δ (Set-ty j)
  _~* p a₀ a₁ = set-curry (_~*' a₀ a₁) p

module _ (Γ : Con i) (A : Ty j Γ) (ρ₀ ρ₁ : Ω ⟶ Γ) (γ₀ γ₁ : Δ ⟶ Ω)
         (p : Tm Δ (El-set ((Ω ~) γ₀ γ₁)))
         (p₀ : Tm Δ (El-set ((Γ ~) (comp-fun γ₀ ρ₀) (comp-fun γ₀ ρ₁))))
         (p₁ : Tm Δ (El-set ((Γ ~) (comp-fun γ₁ ρ₀) (comp-fun γ₁ ρ₁))))
         (r  : Tm Δ (El-prop ((Γ ~~) ρ₀ ρ₁ γ₀ γ₁ p p₀ p₁)))
         (a₀ : Tm Ω (A [ ρ₀ ]))
         (a₁ : Tm Ω (A [ ρ₁ ]))
         (q₀ : Tm Δ (El-set ((A ~*) (comp-fun γ₀ ρ₀) (comp-fun γ₀ ρ₁) p₀
                                    (a₀ [ γ₀ ]') (a₁ [ γ₀ ]'))))
         (q₁ : Tm Δ (El-set ((A ~*) (comp-fun γ₁ ρ₀) (comp-fun γ₁ ρ₁) p₁
                                    (a₀ [ γ₁ ]') (a₁ [ γ₁ ]'))))
         where

  _~~* : Tm Δ (El-set (Prop-set j))
  _~~* = record
    { tm0 = λ δ →
          IxHomEq A (unlift (tm0 r δ)) (tm1 a₀ (tm0 p δ)) (tm1 a₁ (tm0 p δ))
                    (tm0 q₀ δ) (tm0 q₁ δ)
    ; tm1 = λ {γ} {γ'} h →
        let goal : IxHomEq A _ (tm1 a₀ (tm0 p γ)) (tm1 a₁ (tm0 p γ)) (tm0 q₀ γ) (tm0 q₁ γ)
                 ≡ IxHomEq A _ (tm1 a₀ (tm0 p γ')) (tm1 a₁ (tm0 p γ')) (tm0 q₀ γ') (tm0 q₁ γ')
            goal = {!!}
        in lift goal
    ; tm-refl = tt
    ; tm-trans = {!!}
    }
