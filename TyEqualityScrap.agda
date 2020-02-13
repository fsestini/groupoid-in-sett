{-# OPTIONS --prop --rewriting --without-K --allow-unsolved-metas #-}

module TyEqualityScrap where

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
open import Sigma

module _ (A : Ty j Γ) (B : Ty k (Γ ‣ A)) {Δ : Con k}
         {Δ : Con k} (σ : Δ ⟶ Γ) where

  Σ[] : (Sigma A B [ σ ])
      ≡ Sigma (A [ σ ]) (B [ ext (comp-fun (wk (A [ σ ])) σ) (var (A [ σ ])) ])
  Σ[] = sp (λ p → ?) {!!}

-- module _ (A : Ty j Γ) (B : Ty k (Γ ‣ A)) {Δ : Con k}
--   (ρ₀ ρ₁ : Δ ⟶ Γ) (p : Tm Δ (El-set ((Γ ~) ρ₀ ρ₁)))
--   where

--   Σ~ : (Sigma A B ~*) ρ₀ ρ₁ p {!!}
--      ≡ {!!}
--   Σ~ = {!!}
