{-# OPTIONS --prop --rewriting --without-K --allow-unsolved-metas #-}

module Substitution where

open import Data.Product
open import Util
open import Equality
open import Groupoid
open import Ty
open import Tm

_[_] : Ty j Γ -> Δ ⟶ Γ -> Ty j Δ
_[_] {Δ = Δ} A σ = record
  { ∣_∣* = λ δ → ∣ A ∣* (f0 σ δ)
  ; subst* = λ p → subst* A (f1 σ p)
  ; refl*0 = λ x →
      trans {A = ∣ ∣ A ∣* (f0 σ _) ∣}
            (cong (λ z -> f0 (subst* A z) x) (f-R σ)) (refl*0 A _)
  ; refl*1 = λ {γ x y} p → {!!} -- refl*1' A (sym (f-R σ))
  ; trans*0 = λ p q a
      → trans {A = ∣ ∣ A ∣* _ ∣}
          (cong (λ z -> f0 (subst* A z) _) (f-T σ p q))
          (trans*0 A (f1 σ p) (f1 σ q) _)
  ; trans*1 = λ p q r → {!!} -- trans*1' A _ _ _ (sym (f-T σ _ _))
  }

wk : (A : Ty j Γ) -> (Γ ‣ A) ⟶ Γ
wk {Γ = Γ} A =
  record { f0 = proj₁ ; f1 = proj₁
         ; f-R = refl (R Γ _) ; f-T = λ p q → refl (T Γ _ _) }

module _ {A : Ty j Γ} where 

  ext : (σ : Δ ⟶ Γ) -> Tm Δ (A [ σ ]) -> Δ ⟶ (Γ ‣ A)
  ext {Δ = Δ} σ t = record
    { f0 = λ δ → f0 σ δ , tm0 t δ
    ; f1 = λ p → f1 σ p , tm1 t p
    ; f-R = λ { {δ} ->
        let aux : {!!} -- IxHomEq A _ (tm1 t (R Δ δ)) (IxR A (tm0 t δ))
            aux = {!!} -- IxHomEq-T A (IxHomEq-inj A (tm-refl t {δ})) (foobar A (f-R σ))
        in sp (f-R σ) {!tm-refl t {δ}!} -- ‣≡ A (f-R σ) {!!}
      }
    ; f-T = λ p q → sp (f-T σ p q) {!tm-trans t {p = p} {q}!} -- ‣≡ A (f-T σ p q) {!!}
    }

module _ {A : Ty j Γ} where 

  _[_]' : Tm Γ A -> (σ : Δ ⟶ Γ) -> Tm Δ (A [ σ ])
  t [ σ ]' = record
    { tm0 = λ γ → tm0 t (f0 σ γ)
    ; tm1 = λ p → tm1 t (f1 σ p)
    ; tm-refl = λ {δ} -> {!!}
        -- IxHomEq-to-≡' A _ _
        --   (IxHomEq-T A (cong-tm t (f-R σ))
        --    (IxHomEq-T A (IxHomEq-inj A (tm-refl t))
        --      (foobar A (sym (f-R σ)))))
    ; tm-trans = {!!}
       -- λ { {x} {y} {z} {p} {q} → 
       --  IxHomEq-to-≡' A _ _
       --    (IxHomEq-T A (cong-tm t (f-T σ p q))
       --      (IxHomEq-T A (IxHomEq-inj A (tm-trans t {p = f1 σ p} {f1 σ q}))
       --        {!!})) }
    }

wk-ty : (A : Ty k Γ) -> Ty j Γ -> Ty j (Γ ‣ A)
wk-ty A B = B [ wk A ]

wk-tm : (A : Ty k Γ) {B : Ty j Γ} -> Tm Γ B -> Tm (Γ ‣ A) (wk-ty A B)
wk-tm A t = t [ wk A ]'

var : (A : Ty j Γ) -> Tm (Γ ‣ A) (wk-ty A A)
var A = record { tm0 = proj₂ ; tm1 = proj₂
               ; tm-refl = refl (proj₂ (R (_ ‣ A) _))
               ; tm-trans = {!!} }
