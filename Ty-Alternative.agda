{-# OPTIONS --prop --rewriting --without-K --allow-unsolved-metas #-}

module Ty-Alternative where

open import Agda.Builtin.Equality renaming (_≡_ to _⇒_ ; refl to reduce)
open import Agda.Builtin.Equality.Rewrite

open import Data.Product
open import Util
open import Equality
open import Groupoid
open import Ty

record Ty' (j : Level) {i} (Γ : Con i) : Set (i ⊔ lsuc j) where
  field
    ∣_∣*' : ∣ Γ ∣ -> Set j
    Hom* : ∀{γ γ'} -> Hom Γ γ γ' -> ∣_∣*' γ -> ∣_∣*' γ' -> Set j

    R* : ∀{γ} x -> Hom* (R Γ γ) x x
    S* : ∀{γ γ' x y} {p : Hom Γ γ γ'} -> Hom* p x y -> Hom* (S Γ p) y x
    T* : ∀{γ₀ γ₁ γ₂ x y z} {p : Hom Γ γ₀ γ₁} {q : Hom Γ γ₁ γ₂}
       -> Hom* p x y -> Hom* q y z -> Hom* (T Γ p q) x z

    id1*' : ∀{γ γ' x y} {p : Hom Γ γ γ'}
         -> (q : Hom* p x y) -> HEq (λ z → Hom* z _ _) (id1 Γ) (T* q (R* _)) q
    id2*' : ∀{γ γ' x y} {p : Hom Γ γ γ'}
         -> (q : Hom* p x y) -> HEq (λ z → Hom* z _ _) (id2 Γ) (T* (R* _) q) q
    assoc*' : ∀{γ₀ γ₁ γ₂ γ₃ x y z w}
            → {p₀ : Hom Γ γ₀ γ₁} {p₁ : Hom Γ γ₁ γ₂} {p₂ : Hom Γ γ₂ γ₃}
            → (q₀ : Hom* p₀ x y) (q₁ : Hom* p₁ y z) (q₂ : Hom* p₂ z w)
            → HEq (λ z → Hom* z _ _) (assoc Γ) (T* q₀ (T* q₁ q₂)) (T* (T* q₀ q₁) q₂)

    coe* : ∀{γ γ'} (p : Hom Γ γ γ') -> ∣_∣*' γ -> ∣_∣*' γ'
    coh* : ∀{γ γ'} (p : Hom Γ γ γ') (a : ∣_∣*' γ) -> Hom* p a (coe* p a)

    coe*-refl : ∀{γ x} → coe* (R Γ γ) x ≡ x
    coe*-trans : ∀{γ γ' γ'' x} {p : Hom Γ γ γ'} {q : Hom Γ γ' γ''}
               → coe* (T Γ p q) x ≡ coe* q (coe* p x)
open Ty'

module _ (A : Ty' j Γ)
         {γ₀ γ₁ γ₂ x₀ x₁ x₂} {p₀ : Hom Γ γ₀ γ₁} {p₁ p₁' : Hom Γ γ₁ γ₂}
         {r : p₁ ≡ p₁'}
         {q₀ : Hom* A p₀ x₀ x₁}
         {q₁ : Hom* A p₁ x₁ x₂}
       where

  test : T* A q₀ (coe (λ z → Hom* A z x₁ x₂) r q₁)
       ≡ coe (λ z → Hom* A z _ _) (cong (T Γ p₀) r) (T* A q₀ q₁)
  test = {!!}

module _ (A : Ty j Γ) where

  iso1 : Ty' j Γ
  iso1 = record
    { ∣_∣*' = λ γ -> ∣ ∣ A ∣* γ ∣
    ; Hom* = λ p x y → Hom (∣ A ∣* _) (f0 (subst* A p) x) y
    ; R* = λ {γ} x → coe (λ z → Hom (∣ A ∣* _) z _)
                         (sym {A = ∣ ∣ A ∣* _ ∣} (refl*0 A x))
                         (R (∣ A ∣* γ) x)
    ; S* = λ { {p = p} q →
        let open Eq-Reasoning (∣ ∣ A ∣* _ ∣)
            aux = S (∣ A ∣* _) (f1 (subst* A (S Γ p)) q)
        in coe (Hom (∣ A ∣* _) _)
             (tr (sy (trans*0 A p (S Γ p) _))
               (tr (cong (λ z → f0 (subst* A z) _) (inv1 Γ)) (refl*0 A _))) aux }
    ; T* = λ { {p = p1} {p2} q1 q2 →
        let aux = f1 (subst* A p2) q1
        in T (∣ A ∣* _)
             (coe (λ z → Hom (∣ A ∣* _) z (f0 (subst* A _) _))
               (sym {A = ∣ ∣ A ∣* _ ∣} (trans*0 A _ _ _)) aux)
             q2 }
    ; id1*' = λ q → {!!}
    ; id2*' = {!!}
    ; assoc*' = {!!}
    ; coe* = λ p x → f0 (subst* A p) x
    ; coh* = λ p a → R (∣ A ∣* _) _
    ; coe*-refl = {!!}
    ; coe*-trans = {!!}
    }

module _ (A : Ty' j Γ) where

  iso2 : Ty j Γ
  iso2 = record
    { ∣_∣* = λ γ → record
      { ∣_∣ = ∣ A ∣*' γ
      ; Hom = λ x y → Hom* A (R Γ _) x y
      ; R = R* A
      ; S = λ p → coe (λ z → Hom* A z _ _) (S-id Γ) (S* A p)
      ; T = λ p q → coe (λ z → Hom* A z _ _) (id1 Γ) (T* A p q)
      ; id1 = λ {x} {y} {p} → toEq (λ z → Hom* A z _ _) (id1*' A p)
      ; id2 = λ {x} {y} {p} → toEq (λ z → Hom* A z _ _) (id2*' A p)
      ; assoc = λ {x} {y} {z} {w} {p} {q} {r} →
          let goal : HEq (λ z → Hom* A z _ _) _
                       (T* A p (coe (λ z₁ → Hom* A z₁ y w) _ (T* A q r)))
                       (coe (λ z₁ → Hom* A z₁ x w) _ (T* A (coe (λ z₁ → Hom* A z₁ x z) _ (T* A p q)) r))
              goal = {!!}
          in {!!}
                -- toEq (λ z → Hom* A z _ _)
                --   (trans' {A = λ z₁ → Hom* A z₁ _ _} {!assoc*' A p q r!} {!!})
      -- assoc*' A p q r
      ; inv1 = {!!}
      ; inv2 = {!!}
      }
    ; subst* = λ p → record
      { f0 = coe* A p
      ; f1 = λ { {x = x} {y} q →
        let aux = T* A (T* A (S* A (coh* A p x)) q) (coh* A p y)
            t = hom-tr Γ ; s = hom-sy Γ
            eq : T Γ (T Γ (S Γ p) (R Γ _)) p ≡ R Γ _
            eq = t (cong (λ z → T Γ z p) (id1 Γ)) (inv2 Γ)
        in coe (λ z → Hom* A z _ _) eq aux
        }
      ; f-R = {!!}
      ; f-T = λ q1 q2 → {!!}
      }
    ; refl*0 = λ x → coe*-refl A
    ; refl*1 = λ p → {!!}
    ; trans*0 = λ p q a → coe*-trans A
    ; trans*1 = {!!}
    }
