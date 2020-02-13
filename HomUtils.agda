{-# OPTIONS --prop --rewriting --without-K --allow-unsolved-metas #-}

module HomUtils where

open import Data.Product
open import Util
open import Equality
open import Groupoid
open import Ty

substMorph : (Γ : Groupoid i) {a b c : _} -> a ≡ c -> Hom Γ a b -> Hom Γ c b
substMorph Γ r p = coe (λ z → Hom Γ z _) r p

