{-# OPTIONS --prop --without-K --rewriting --allow-unsolved-metas #-}

module Sigma where

open import Lib
open import SetoidEquality
open import Groupoid
open import Substitution
open import Ty
open import Tm
open import Universes

module _ (A : Ty j Γ) (B : Ty k (Γ ‣ A)) where

  ff : ∀ γ → ∣ A ∣* γ ⟶ (Γ ‣ A)
  ff γ = record
    { f0 = γ ,_
    ; f1 = λ x → R Γ γ , Hom-to-IxHom A x
    ; f-R = {!!}
    ; f-T = {!!}
    }

  private
    B' : ∀ γ → Ty k (∣ A ∣* γ)
    B' γ = B [ ff γ ]

  module _ {x y : ∣ Γ ∣} (p : Hom Γ x y) where

    uwu : Tm (∣ A ∣* x ‣ (B [ ff x ])) (B [ comp-fun (wk (B' x)) (comp-fun (subst* A p) (ff y)) ])
    uwu = record
      { tm0 = λ { (a , b) → f0 (subst* B (p , R (∣ A ∣* y) _)) b }
      ; tm1 = {!!}
      ; tm-refl = {!!}
      }

    func : (∣ A ∣* x ‣ B' x) ⟶ (∣ A ∣* y ‣ B' y)
    func =
      ext {Γ = ∣ A ∣* y} {B' y} {_} {∣ A ∣* x ‣ B' x}
        (comp-fun (wk (B' x)) (subst* A p)) uwu

  Sigma : Ty _ Γ
  Sigma = record
    { ∣_∣* = λ γ → ∣ A ∣* γ ‣ B' γ
    ; subst* = func
        --      λ {γ} {γ'} p →
        -- let f : (∣ A ∣* γ ‣ B' γ) ⟶ ∣ A ∣* γ'
        --     f = comp-fun (wk (B' γ)) (subst* A p)
        --     aux : Tm (∣ A ∣* γ ‣ B' γ) (B' γ' [ f ])
        --     aux = record
        --       { tm0 = λ { (a , b) → f0 (subst* B (p , (R (∣ A ∣* γ') _))) b }
        --       ; tm1 = λ { {a , b} {a' , b'} (q1 , q2) →
        --            let ty = (B' γ' [ comp-fun (wk (B' γ)) (subst* A p) ])
        --                aux1' : IxHomEq A (HomEq-R Γ p)
        --                          (Hom-to-IxHom A q1) (Hom-to-IxHom A (f1 (subst* A p) q1))
        --                          (R (∣ A ∣* γ') (f0 (subst* A p) a))
        --                          (R (∣ A ∣* γ') (f0 (subst* A p) a'))
        --                aux1' = {!f1 (subst* A p) q1!}
        --                aux1 : HomEq (Γ ‣ A) (R Γ _ , {!!}) (R Γ _ , {!!})
        --                         (p , R (∣ A ∣* γ') (f0 (subst* A p) a))
        --                         (p , R (∣ A ∣* γ') (f0 (subst* A p) a'))
        --                aux1 = HomEq-R Γ p ,p aux1'
        --                aux2 : IxHom B _ b b'
        --                aux2 = q2
        --                goal : IxHom B _
        --                         (f0 (subst* B (p , R (∣ A ∣* γ') (f0 (subst* A p) a))) b)
        --                         (f0 (subst* B (p , R (∣ A ∣* γ') (f0 (subst* A p) a'))) b')
        --                goal = transp-IxHom B {!!} (subst*-eq B aux1 aux2)
        --             in goal
        --           }
        --       ; tm-refl = {!!}
        --       -- ; tm-trans = {!!}
        --       }
        -- in ext (comp-fun (wk (B' γ)) (subst* A p)) aux
    ; refl*0 = λ x → refl*0 A _ ,p {!!}
    ; refl*1 = {!!}
    ; trans*0 = λ p q a → trans*0 A _ _ _ ,p {!!}
    ; trans*1 = {!!}
    }

module _ {A A' : Set i} {B : A -> Set j} {B' : A' -> Set j} where

  Σ-iso : (p : Iso A A') -> ((a : A) -> Iso (B a) (B' (iso1 p a)))
        -> Iso (Σ A B) (Σ A' B')
  Σ-iso isoA isoB = record
    { iso1 = λ { (a , b) → iso1 isoA a , iso1 (isoB a) b }
    ; iso2 = λ { (a' , b') → iso2 isoA a' , iso2 (isoB (iso2 isoA a')) (coe B' (sym A' (prf2 isoA a')) b') }
    ; prf1 = λ { (a , b) → prf1 isoA a ,p {!!} }
    ; prf2 = λ { (a' , b') → prf2 isoA a' ,p {!!} }
    }

module _ {j k} (A : Tm Γ (Set-ty j)) (B : Tm (Γ ‣ El-set A) (Set-ty k)) where

  Sigma-set : Tm Γ (Set-ty (j ⊔ k))
  Sigma-set = record
    { tm0 = λ γ → Σ (tm0 A γ) λ a → tm0 B (γ , a)
    ; tm1 = λ p → Σ-iso (tm1 A p) (λ a → tm1 B (p , prf (refl _ (iso1 (tm1 A p) a))))
    ; tm-refl = {!!}
--    ; tm-trans = {!!}
    }
