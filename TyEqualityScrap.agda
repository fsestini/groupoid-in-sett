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
         {Δ : Con k} (σ : Δ ⟶ Γ) {δ : ∣ Δ ∣}
         (p q : Σ ∣ ∣ A ∣* (f0 σ δ) ∣ (λ a → ∣ ∣ B ∣* (f0 σ δ , a) ∣)) where

  aaa : Hom (∣ Sigma A B [ σ ] ∣* δ) p q
      ≡ Hom (∣ Sigma (A [ σ ]) (B [ ext (comp-fun (wk (A [ σ ])) σ) (var (A [ σ ])) ]) ∣* δ) p q
  aaa = cong (Σ (Hom (∣ A ∣* (f0 σ δ)) (proj₁ p) (proj₁ q)))
             λ p → cong (λ z → Hom (∣ B ∣* (f0 σ δ , proj₁ q)) z (proj₂ q))
               {!!}

-- (R Γ (f0 σ δ) , coe (λ z → Hom (∣ A ∣* (f0 σ δ)) z (proj₁ b)) _ a₁)

-- (f1 σ (R Δ δ) , coe (λ z → Hom (∣ A ∣* (f0 σ δ)) z (proj₁ b)) _ a')
