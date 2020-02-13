{-# OPTIONS --prop --rewriting --without-K --allow-unsolved-metas #-}

module Universes where

open import Agda.Builtin.Equality renaming (_≡_ to _⇒_ ; refl to reduce)
open import Agda.Builtin.Equality.Rewrite

open import Data.Product
open import Util
open import Equality
open import Groupoid
open import Substitution
open import Ty
open import Tm

private
  variable A B C : Set i

record Iso (A B : Set i) : Set (lsuc i) where
  field
    iso1 : A -> B
    iso2 : B -> A
    prf1 : (x : A) -> iso2 (iso1 x) ≡ x
    prf2 : (x : B) -> iso1 (iso2 x) ≡ x
open Iso public

iso-R : Iso A A
iso-R = record
  { iso1 = λ z → z ; iso2 = λ z → z ; prf1 = refl ; prf2 = refl }

iso-S : Iso A B -> Iso B A
iso-S i = record
  { iso1 = iso2 i
  ; iso2 = iso1 i
  ; prf1 = prf2 i
  ; prf2 = prf1 i
  }

iso-T : Iso A B -> Iso B C -> Iso A C
iso-T {A = A} {C = C} i1 i2 = record
  { iso1 = λ x → iso1 i2 (iso1 i1 x)
  ; iso2 = λ x → iso2 i1 (iso2 i2 x)
  ; prf1 = λ x → trans {A = A} (cong (iso2 i1) (prf1 i2 (iso1 i1 x))) (prf1 i1 x)
  ; prf2 = λ x → trans {A = C} (cong (iso1 i2) (prf2 i1 (iso2 i2 x))) (prf2 i2 x)
  }

postulate
  Iso≡ : {A B : Set i} {f g : Iso A B}
       → _≡_ {A = Iso A B} f g
       ⇒ ΣP' (iso1 f ≡ iso1 g) λ _ → iso2 f ≡ iso2 g
{-# REWRITE Iso≡ #-}

const-ty : Groupoid j -> Ty j Γ
const-ty G = record
  { ∣_∣* = λ _ → G
  ; subst* = λ x →
      record { f0 = λ x → x ; f1 = λ x → x ; f-R = refl (R G _) ; f-T = λ _ _ → refl (T G _ _) }
  ; refl*0 = refl
  ; refl*1 = λ p → refl p
  ; trans*0 = λ _ _ → refl
  ; trans*1 = λ p q r → refl _
  }

Set-ty : (j : Level) -> Ty (lsuc j) Γ
Set-ty j = const-ty (record
  { ∣_∣ = Set j
  ; Hom = Iso
  ; R = λ x → iso-R
  ; S = λ p → record
    { iso1 = iso2 p ; iso2 = iso1 p ; prf1 = prf2 p ; prf2 = prf1 p }
  ; T = λ {x = A} {B} {C} p q → record
    { iso1 = λ x -> iso1 q (iso1 p x) ; iso2 = λ x → iso2 p (iso2 q x)
    ; prf1 = λ x → trans {A = A} (cong (iso2 p) (prf1 q (iso1 p x))) (prf1 p x)
    ; prf2 = λ x → trans {A = C} (cong (iso1 q) (prf2 p (iso2 q x))) (prf2 q x)
    }
  ; id1 = λ { {p = p} → refl p }
  ; id2 = λ { {p = p} → refl p }
  ; assoc = λ { {p = p} {q} {r} → refl (iso-T (iso-T p q) r) }
  ; inv1 = λ { {x = A} {p = p} -> let open Eq-Reasoning A in
      sp' (λ q → tr (prf1 p _) q) (λ q → tr (prf1 p _) q) }
  ; inv2 = λ { {x = A} {B} {p = p} -> let open Eq-Reasoning B in
      sp' (λ q → tr (prf2 p _) q) (λ q → tr (prf2 p _) q) }
  })

discrete : Set j -> Groupoid j
discrete S = record
  { ∣_∣ = S
  ; Hom = λ x y → Lift (x ≡ y)
  ; R = λ x -> lift (refl x)
  ; S = λ { (lift p) → lift (sym {A = S} p) }
  ; T = λ { (lift p) (lift q) → lift (trans {A = S} p q) }
  ; id1 = tt
  ; id2 = tt
  ; assoc = tt
  ; inv1 = tt
  ; inv2 = tt
  }

El-set : Tm Γ (Set-ty j) -> Ty j Γ
El-set {Γ = Γ} {j = j} t = record
  { ∣_∣* = λ γ → discrete (tm0 t γ)
  ; subst* = λ {γ} {γ'} p → record
    { f0 = iso1 (tm1 t p)
    ; f1 = λ{ (lift eq) → lift (cong (iso1 (tm1 t p)) eq) }
    ; f-R = tt
    ; f-T = λ _ _ → tt
    }
  ; refl*0 = λ {γ = γ} x →
     cong (λ z -> iso1 z x) {tm1 t _} {IxR {Γ = Γ} (Set-ty j) {γ} _} (tm-refl t {γ})
  ; refl*1 = λ _ → tt
  ; trans*0 = λ p q a →
      let goal1 : iso1 (tm1 t (T Γ p q)) a ≡ iso1 (IxT (Set-ty j) (tm1 t p) (tm1 t q)) a
          goal1 = cong (λ z → iso1 z a) (tm-trans t {p = p} {q})
          goal2 : iso1 (IxT (Set-ty j) (tm1 t p) (tm1 t q)) a ≡ iso1 (tm1 t q) (iso1 (tm1 t p) a)
          goal2 = {!tm1 t p!}
      in trans {A = tm0 t _} goal1 goal2
    -- λ p q a →
    --   cong (λ z -> iso1 z a) (tm-trans t {p = p} {q})
    --     ∙ cong (iso1 (tm1 t q)) (transportRefl _
    --     ∙ cong (iso1 (tm1 t p)) (transportRefl _))
  ; trans*1 = λ _ _ _ → tt
  }

module _ (A : Tm Γ (Set-ty j)) where

  IxSetEq : ∀{γ γ'} -> Hom Γ γ γ' -> tm0 A γ → tm0 A γ' → Prop j
  IxSetEq p x y = iso1 (tm1 A p) x ≡ y

Prop-set : (j : Level) -> Tm Γ (Set-ty (lsuc j))
Prop-set j = record
  { tm0 = λ γ → Prop j
  ; tm1 = λ _ → iso-R
  ; tm-refl = refl iso-R
  ; tm-trans = sp' {!!} {!!}
  }

-- module _ {Γ : Con i} (A : Tm Γ (El-set (Prop-set j))) where

--   IxPropEq : ∀{γ γ'} -> Hom Γ γ γ' -> tm0 A γ -> tm0 A γ' -> {!!}
--   -- fst (tm0 A γ) → fst (tm0 A γ') → Set j
--   IxPropEq {γ = γ} {γ'} p x y = {!!} -- coe fst (tm1 A p) x ≡ y


El-prop-into-set : Tm Γ (El-set (Prop-set j)) -> Tm Γ (Set-ty j)
El-prop-into-set M = record
  { tm0 = λ γ → Lift (tm0 M γ)
  ; tm1 = λ {γ = γ} {γ'} p →
      coe (λ z → Iso (Lift (tm0 M γ)) (Lift z)) (unlift (tm1 M p)) iso-R
  ; tm-refl = refl iso-R
  ; tm-trans = {!!}
  }
  
El-prop : Tm Γ (El-set (Prop-set j)) -> Ty j Γ
El-prop M = El-set (El-prop-into-set M)

module _ {Γ : Con i} {A : Ty j Γ} (t : Tm (Γ ‣ A) (Set-ty k)) where

  set-curry : (a : Tm Γ A) -> Tm Γ (Set-ty k)
  set-curry a = record
    { tm0 = λ γ → tm0 t (γ , tm0 a γ)
    ; tm1 = λ p → tm1 t (p , tm1 a p)
    ; tm-refl = {!!}
    ; tm-trans = {!!}
    }
