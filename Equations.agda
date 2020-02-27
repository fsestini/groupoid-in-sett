{-# OPTIONS --prop --rewriting --without-K #-}

module Equations where

open import Data.Product
open import Util
open import Equality
open import Groupoid
open import Ty
open import Tm
open import Substitution
open import Universes
open import CtxEquality
open import TyEquality
open import Sigma

module _ {A : Ty j Γ} {σ : Δ ⟶ Γ} {γ γ' : _} {p : Hom Δ γ γ'}
         {a : ∣ ∣ A ∣* (f0 σ γ) ∣} {a' : ∣ ∣ A ∣* (f0 σ γ') ∣} where

  IxHom[] : IxHom (A [ σ ]) p a a' ≡ IxHom A (f1 σ p) a a'
  IxHom[] = refl (IxHom (A [ σ ]) p a a')

[id] : (A : Ty j Γ) -> (A [ id-fun Γ ]) ≡ A
[id] A = refl A

[][] : (A : Ty j Γ) (σ : Δ ⟶ Γ) (γ : ∇ ⟶ Δ) -> (A [ σ ] [ γ ]) ≡ (A [ comp-fun γ σ ])
[][] A σ γ = refl ((A [ σ ]) [ γ ])

[]'[]' : {A : Ty j Γ} (t : Tm Γ A) (σ : Δ ⟶ Γ) (γ : ∇ ⟶ Δ)
       → (t [ σ ]' [ γ ]') ≡ (t [ comp-fun γ σ ]')
[]'[]' t σ γ = refl ((t [ σ ]') [ γ ]')

-- -- Universes

-- module _ {Γ : Con i} {γ γ' : ∣ Γ ∣} {p : Hom Γ γ γ'} {A B : Set j} where

--   IxHom-Set-ty : IxHom (Set-ty {Γ = Γ} j) p A B ≡ Iso A B
--   IxHom-Set-ty = refl (Iso A B)

-- Set[] : (σ : Δ ⟶ Γ) -> (Set-ty j [ σ ]) ≡ Set-ty j
-- Set[] {j = j} σ = refl (Set-ty j [ σ ])

-- module _ {A : Tm Γ (Set-ty j)} {γ₀ γ₁} {p : Hom Γ γ₀ γ₁}
--          {a₀ : tm0 A γ₀} {a₁ : tm0 A γ₁} where

--   IxHomEl : IxHom (El-set A) p a₀ a₁ ≡ Lift (IxSetEq A p a₀ a₁)
--   IxHomEl = refl (IxHom (El-set A) p a₀ a₁)

-- module _ {Γ : Con i} {A : Tm Γ (Set-ty j)} (σ : Δ ⟶ Γ) where

--   El[] : ((El-set A) [ σ ]) ≡ El-set (A [ σ ]')
--   El[] = refl ((El-set A) [ σ ])

-- -- module _ {Γ : Con i} {A B C : Set j}
-- --          {γ₀ γ₁} {p : Hom Γ γ₀ γ₁}
-- --          {γ₁'} {p' : Hom Γ γ₁ γ₁'}
-- --          {i1 : Iso A B} {i2 : Iso B C}
-- --          where

-- --   uhmiso : IxT (Set-ty {Γ = Γ} j) {p = p} {q = p'} i1 i2
-- --          ≡ {!!}
-- --          -- iso-T i1 i2
-- --   uhmiso = refl (IxT (Set-ty {Γ = Γ} j) {p = p} {q = p'} i1 i2)

-- Prop[] : ∀{j} (σ : Δ ⟶ Γ) -> ((Prop-set j) [ σ ]') ≡ Prop-set j
-- Prop[] {j = j} σ = refl ((Prop-set j) [ σ ]')

-- module _ {Γ : Con i} {γ γ'} (m : Hom Γ γ γ') {P Q : Prop j} where

--   IxSetProp : IxSetEq (Prop-set {Γ = Γ} j) m P Q ≡ ΣP' (P → Q) (λ _ → Q → P)
--   IxSetProp = refl (IxSetEq (Prop-set {Γ = Γ} j) m P Q)

-- module _ {Γ : Con i} {A : Tm Γ (El-set (Prop-set j))} (σ : Δ ⟶ Γ) where

--   Elp[] : ((El-prop-into-set A) [ σ ]') ≡ El-prop-into-set (A [ σ ]')
--   Elp[] = refl ((El-prop-into-set A) [ σ ]')

-- -- Context equality

-- module _ {Γ : Con i} {γ₀ γ₁ : Δ ⟶ Γ} {ρ : Ω ⟶ Δ} where

--   Γ~[] : (((Γ ~) γ₀ γ₁) [ ρ ]') ≡ (Γ ~) (comp-fun ρ γ₀) (comp-fun ρ γ₁)
--   Γ~[] = refl (((Γ ~) γ₀ γ₁) [ ρ ]')

-- module _ {ρ : Δ ⟶ Γ} {γ : Ω ⟶ Δ} where

--   R~[] : ((R~ ρ) [ γ ]') ≡ R~ (comp-fun γ ρ)
--   R~[] = refl (R~ ρ [ γ ]')

-- module _ {γ₀ γ₁ : Δ ⟶ Γ} {p : Tm Δ (El-set ((Γ ~) γ₀ γ₁))} {ρ : Ω ⟶ Δ} where

--   S~[] : ((S~ γ₀ γ₁ p) [ ρ ]') ≡ S~ (comp-fun ρ γ₀) (comp-fun ρ γ₁) (p [ ρ ]')
--   S~[] = refl ((S~ γ₀ γ₁ p) [ ρ ]')

-- module _ {γ₀ γ₁ γ₂ : Δ ⟶ Γ}
--          {p : Tm Δ (El-set ((Γ ~) γ₀ γ₁))}
--          {q : Tm Δ (El-set ((Γ ~) γ₁ γ₂))}
--          {ρ : Ω ⟶ Δ} where

--   T~[] : (T~ γ₀ γ₁ γ₂ p q [ ρ ]')
--        ≡ T~ (comp-fun ρ γ₀) (comp-fun ρ γ₁) (comp-fun ρ γ₂) (p [ ρ ]') (q [ ρ ]')
--   T~[] = refl (T~ γ₀ γ₁ γ₂ p q [ ρ ]')

-- module _ {∇ : Con i} {Δ : Con k} (Γ : Con i) (ρ₀ ρ₁ : Ω ⟶ Γ) (γ₀ γ₁ : Δ ⟶ Ω)
--          (p : Tm Δ (El-set ((Ω ~) γ₀ γ₁)))
--          (r₀ : Tm Δ (El-set ((Γ ~) (comp-fun γ₀ ρ₀) (comp-fun γ₀ ρ₁))))
--          (r₁ : Tm Δ (El-set ((Γ ~) (comp-fun γ₁ ρ₀) (comp-fun γ₁ ρ₁))))
--          (τ : ∇ ⟶ Δ)
--          where

--   ~~[] : (((Γ ~~) ρ₀ ρ₁ γ₀ γ₁ p r₀ r₁) [ τ ]')
--        ≡ (Γ ~~) ρ₀ ρ₁ (comp-fun τ γ₀) (comp-fun τ γ₁) (p [ τ ]') (r₀ [ τ ]') (r₁ [ τ ]')
--   ~~[] = refl (((Γ ~~) ρ₀ ρ₁ γ₀ γ₁ p r₀ r₁) [ τ ]')

-- module _ {Γ : Con i} {ρ₀ ρ₁ : Δ ⟶ Γ}
--          {δ₀ δ₁} {p : Hom Δ δ₀ δ₁}
--          {t₀ : Hom Γ (f0 ρ₀ δ₀) (f0 ρ₁ δ₀)}
--          {t₁ : Hom Γ (f0 ρ₀ δ₁) (f0 ρ₁ δ₁)}
--          where

--   IxSetEq~ : IxSetEq ((Γ ~) ρ₀ ρ₁) p t₀ t₁
--            ≡ HomEq Γ (f1 ρ₀ p) (f1 ρ₁ p) t₀ t₁
--   IxSetEq~ = refl (IxSetEq ((Γ ~) ρ₀ ρ₁) p t₀ t₁)

-- module _ (Γ : Con i) (A : Ty j Γ) {Δ : Con k}
--          (ρ₀ ρ₁ : Δ ⟶ Γ) (a₀ : Tm Δ (A [ ρ₀ ])) (a₁ : Tm Δ (A [ ρ₁ ]))
--          where

--   ‣-~ : ((Γ ‣ A) ~) (ext ρ₀ a₀) (ext ρ₁ a₁)
--       ≡ Sigma-set ((Γ ~) ρ₀ ρ₁) ((A ~*') ρ₀ ρ₁ a₀ a₁)
--   ‣-~ = refl (((Γ ‣ A) ~) (ext ρ₀ a₀) (ext ρ₁ a₁))

-- -- Type equality

-- module _ {Γ : Con i} {Δ : Con k} (A : Ty j Γ) (γ₀ γ₁ : Δ ⟶ Γ)
--          (p : Tm Δ (El-set ((Γ ~) γ₀ γ₁)))
--          (a₀ : Tm Δ (A [ γ₀ ])) (a₁ : Tm Δ (A [ γ₁ ]))
--          {δ₀ δ₁} (q : Hom Δ δ₀ δ₁)
--          (t₀ : tm0 ((A ~*) γ₀ γ₁ p a₀ a₁) δ₀)
--          (t₁ : tm0 ((A ~*) γ₀ γ₁ p a₀ a₁) δ₁)
--          where

--   IxSetEq~* : IxSetEq ((A ~*) γ₀ γ₁ p a₀ a₁) q t₀ t₁
--             ≡ IxHomEq A (unlift (tm1 p q)) (tm1 a₀ q) (tm1 a₁ q) t₀ t₁
--   IxSetEq~* = refl (IxSetEq ((A ~*) γ₀ γ₁ p a₀ a₁) q t₀ t₁)

-- -- Sigma

-- module _ {j k} (A : Tm Γ (Set-ty j)) (B : Tm (Γ ‣ El-set A) (Set-ty k))
--          {Δ : Con k} (σ : Δ ⟶ Γ)
--          where

--   Σₛ[] : (Sigma-set A B [ σ ]')
--        ≡ Sigma-set (A [ σ ]') (B [ ext (comp-fun (wk (El-set (A [ σ ]'))) σ) (var (El-set (A [ σ ]'))) ]')
--   Σₛ[] = refl (Sigma-set A B [ σ ]')
