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

[id] : (A : Ty j Γ) -> (A [ id-fun Γ ]) ≡ A
[id] A = refl A

wk : (A : Ty j Γ) -> (Γ ‣ A) ⟶ Γ
wk {Γ = Γ} A =
  record { f0 = proj₁ ; f1 = proj₁
         ; f-R = refl (R Γ _) ; f-T = λ p q → refl (T Γ _ _) }

[][] : (A : Ty j Γ) (σ : Δ ⟶ Γ) (γ : ∇ ⟶ Δ) -> (A [ σ ] [ γ ]) ≡ (A [ comp-fun γ σ ])
[][] A σ γ = refl ((A [ σ ]) [ γ ])

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

module _ {A P : Ty j Γ} {p : Tm Γ P} {a : Tm Γ A} where

  foo : (p [ wk A ]' [ ext (id-fun Γ) a ]') ≡ p
  foo = refl p

module _ {A : Ty j Γ} where
  [][]' : (t : Tm Γ A) (σ : Δ ⟶ Γ) (γ : ∇ ⟶ Δ)
        -> HEq (Tm ∇) ([][] A σ γ) ((t [ σ ]') [ γ ]') (t [ comp-fun γ σ ]')
  [][]' {∇ = ∇} t σ γ = refl' {A = Tm ∇} ((t [ σ ]') [ γ ]')


module _ {A : Ty j Γ} {σ : Δ ⟶ Γ} {γ γ' : _} {p : Hom Δ γ γ'}
         {a : ∣ ∣ A ∣* (f0 σ γ) ∣} {a' : ∣ ∣ A ∣* (f0 σ γ') ∣} where

  IxHom[] : IxHom (A [ σ ]) p a a' ≡ IxHom A (f1 σ p) a a'
  IxHom[] = refl (IxHom (A [ σ ]) p a a')

-- module _ {A : Ty j Γ} {σ : Δ ⟶ Γ} {δ : _} {a : ∣ ∣ A ∣* (f0 σ δ) ∣ } where

--   uhmm : HEq (λ z → Hom (∣ A ∣* (f0 σ δ)) (f0 (subst* A z) a) a) (f-R σ)
--       (coe (λ z → Hom (∣ A ∣* (f0 σ δ)) z a) {!!} (R (∣ A ∣* (f0 σ δ)) a))
--       (coe (λ z → Hom (∣ A ∣* (f0 σ δ)) z a) {!!} (R (∣ A ∣* (f0 σ δ)) a))
--   uhmm = fromEq (λ z → Hom (∣ A ∣* (f0 σ δ)) (f0 (subst* A z) a) a) {!!}

--   IxR[] : HEq (λ z -> IxHom A z a a) (f-R σ) (IxR (A [ σ ]) a) (IxR A a)
--   IxR[] = uhmm

-- -- IxR (A [ σ ]) a : IxHom A (f1 σ (R Δ δ)) a a
-- -- IxR A a : IxHom A (R Γ (f0 σ δ)) a a

