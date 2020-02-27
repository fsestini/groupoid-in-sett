{-# OPTIONS --prop --without-K --rewriting --allow-unsolved-metas #-}

module Sigma where

open import Data.Product
open import Util
open import Equality
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

  -- private
  --   B' : ∀ γ → Ty k (∣ A ∣* γ)
  --   B' γ = record
  --     { ∣_∣* = λ a → ∣ B ∣* (γ , a)
  --     ; subst* = λ {x} {y} p →
  --          subst* B (R Γ γ , coe (λ z → Hom (∣ A ∣* _) z _)
  --                               (sym {A = ∣ ∣ A ∣* _ ∣} (refl*0 A x) ) p)
  --     ; refl*0 = refl*0 B
  --     ; refl*1 = refl*1 B
  --     ; trans*0 = λ p q a →
  --         let aux =
  --              trans*0 B (R Γ _ , Hom-to-IxHom A p) (R Γ _ , (Hom-to-IxHom A q)) a
  --             s = hom-sy Γ ; t = hom-tr Γ ; _∙_ = trans {A = ∣ ∣ B ∣* (γ , _) ∣}
  --         in cong (λ x → f0 (subst* B x) a) (sp (s (id1 Γ)) {!!}) ∙ aux
  --     ; trans*1 = {!!}
  --     }

  Sigma : Ty _ Γ
  Sigma = record
    { ∣_∣* = λ γ → ∣ A ∣* γ ‣ B' γ
    ; subst* = λ {γ} {γ'} p →
        let f : (∣ A ∣* γ ‣ B' γ) ⟶ ∣ A ∣* γ'
            f = comp-fun (wk (B' γ)) (subst* A p)
            aux : Tm (∣ A ∣* γ ‣ B' γ) (B' γ' [ f ])
            aux = record
              { tm0 = λ { (a , b) → f0 (subst* B (p , (R (∣ A ∣* γ') _))) b }
              ; tm1 = λ { {a , b} {a' , b'} (q1 , q2) →
                   let ty = (B' γ' [ comp-fun (wk (B' γ)) (subst* A p) ])
                       aux1' : IxHomEq A (HomEq-R Γ p)
                                 (Hom-to-IxHom A q1) (Hom-to-IxHom A (f1 (subst* A p) q1))
                                 (R (∣ A ∣* γ') (f0 (subst* A p) a))
                                 (R (∣ A ∣* γ') (f0 (subst* A p) a'))
                       aux1' = {!f1 (subst* A p) q1!}
                       aux1 : HomEq (Γ ‣ A) (R Γ _ , {!!}) (R Γ _ , {!!})
                                (p , R (∣ A ∣* γ') (f0 (subst* A p) a))
                                (p , R (∣ A ∣* γ') (f0 (subst* A p) a'))
                       aux1 = sp (HomEq-R Γ p) aux1'
                       aux2 : IxHom B _ b b'
                       aux2 = q2
                       goal : IxHom B _
                                (f0 (subst* B (p , R (∣ A ∣* γ') (f0 (subst* A p) a))) b)
                                (f0 (subst* B (p , R (∣ A ∣* γ') (f0 (subst* A p) a'))) b')
                       goal = transp-IxHom B {!!} (subst*-eq B aux1 aux2)
                    in goal
                  }
              ; tm-refl = {!!}
              ; tm-trans = {!!}
              }
        in ext (comp-fun (wk (B' γ)) (subst* A p)) aux
    ; refl*0 = λ x → sp (refl*0 A _) {!!}
    ; refl*1 = {!!}
    ; trans*0 = λ p q a → sp (trans*0 A _ _ _) {!!}
    ; trans*1 = {!!}
    }

module _ {j k} (A : Tm Γ (Set-ty j)) (B : Tm (Γ ‣ El-set A) (Set-ty k)) where

  Sigma-set : Tm Γ (Set-ty (j ⊔ k))
  Sigma-set = record
    { tm0 = λ γ → Σ (tm0 A γ) λ a → tm0 B (γ , a)
    ; tm1 = λ p → record
      { iso1 = λ { (x , y)
          → iso1 (tm1 A p) x
          , iso1 (tm1 B (p , lift (refl (iso1 (tm1 A p) x)))) y
          }
      ; iso2 = λ { (x , y)
          → iso2 (tm1 A p) x
          , iso2 (tm1 B (p , lift (prf2 (tm1 A p) _))) y
          }
      ; prf1 = {!!}
      ; prf2 = {!!}
      }
    ; tm-refl = {!!}
    ; tm-trans = {!!}
    }
