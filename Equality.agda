{-# OPTIONS --prop --rewriting --without-K #-}

module Equality where

open import Agda.Builtin.Equality renaming (_≡_ to _⇒_ ; refl to reduce)
open import Agda.Builtin.Equality.Rewrite
open import Data.Product
open import Util

postulate
  _≡_ : {A : Set i} -> A -> A -> Prop i

  refl : {A : Set i} (a : A) -> a ≡ a
  sym : {A : Set i} {a a' : A} -> a ≡ a' -> a' ≡ a
  trans : {A : Set i} {a a' a'' : A} -> a ≡ a' -> a' ≡ a'' -> a ≡ a''

  HEq : {I : Set i} (A : I -> Set j) {x y : I} -> x ≡ y -> A x -> A y -> Prop j

  refl' : {I : Set i} {A : I -> Set j} {x : I} {p : x ≡ x} (a : A x) -> HEq A p a a
  sym' : {I : Set i} {A : I -> Set j} {x y : I} {p : x ≡ y} {a : A x} {a' : A y}
     -> HEq A p a a' -> HEq A (sym p) a' a
  trans' : {I : Set i} {A : I -> Set j} {x y z : I} {p : x ≡ y} {q : y ≡ z}
       {a : A x} {a' : A y} {a'' : A z}
     -> HEq A p a a' -> HEq A q a' a'' -> HEq A (trans p q) a a''

  coe : {I : Set i} (A : I -> Set j) {x y : I} (p : x ≡ y) -> A x -> A y
  coh : {I : Set i} (A : I -> Set j) {x y : I} (p : x ≡ y) (a : A x)
      -> HEq A p a (coe A p a)

  Eq-Σ : {A : Set i} {B : A -> Set j} {p q : Σ A B}
       -> _≡_ {A = Σ A B} p q ⇒ ΣP (proj₁ p ≡ proj₁ q) λ r → HEq B r (proj₂ p) (proj₂ q)
  Eq-Π : {A : Set i} {B : A -> Set j} {f g : (a : A) -> B a}
       -> _≡_ {A = (a : A) -> B a} f g ⇒ ({a a' : A} (p : a ≡ a') -> HEq B p (f a) (g a'))
  Eq-Prop : {P Q : Prop i} -> _≡_ {A = Prop i} P Q ⇒ ΣP' (P -> Q) λ _ -> Q -> P
  Eq-Lift : {P : Prop i} {p q : P}
          -> _≡_ {A = Lift P} (lift p) (lift q) ⇒ ⊤

{-# REWRITE Eq-Σ Eq-Π Eq-Prop Eq-Lift #-}

postulate
  HEq-Σ : {I : Set k} {A : I -> Set i} {B : (i : I) -> A i -> Set j}
          {x y : I} {r : x ≡ y} {p : Σ (A x) (B x)} {q : Σ (A y) (B y)}
        -> HEq (λ i → Σ (A i) (B i)) r p q
         ⇒ ΣP (HEq A r (proj₁ p) (proj₁ q)) λ r' →
               HEq {I = Σ I A} (λ { w → B (proj₁ w) (proj₂ w) }) (sp r r') (proj₂ p) (proj₂ q)

  HEq-Π : {I : Set k} {A : I -> Set i} {B : (i : I) -> A i -> Set j}
          {x y : I} {r : x ≡ y} {f : (a : A x) -> B x a} {g : (a : A y) -> B y a}
        -> HEq (λ i → (a : A i) -> B i a) r f g
         ⇒ ({a : A x} {a' : A y} (r' : HEq A r a a')
             -> HEq {I = Σ I A} (λ w → B (proj₁ w) (proj₂ w)) (sp r r') (f a) (g a'))

  HEq-Π' : {I : Set k} {A : I -> Set i} {B : (i : I) -> A i -> Set j}
          {x y : I} {r : x ≡ y} {f : {a : A x} -> B x a} {g : {a : A y} -> B y a}
        -> HEq (λ i → {a : A i} -> B i a) r f g
         ⇒ ({a : A x} {a' : A y} (r' : HEq A r a a')
             -> HEq {I = Σ I A} (λ w → B (proj₁ w) (proj₂ w)) (sp r r') (f {a}) (g {a'}))

  HEq-Lift : {I : Set k} {P : I -> Prop i} {x y : I} {p : P x} {q : P y} {r : x ≡ y}
           -> HEq {I = I} (λ i → Lift (P i)) r (lift p) (lift q) ⇒ ⊤

  coe-Σ : {I : Set k} {A : I -> Set i} {B : (i : I) -> A i -> Set j}
          {x y : I} {r : x ≡ y} {p : Σ (A x) (B x)}
        -> coe (λ i → Σ (A i) (B i)) r p
         ⇒ ( coe A r (proj₁ p)
           , coe {I = Σ I A} (λ w → B (proj₁ w) (proj₂ w)) (sp r (coh A _ _)) (proj₂ p))

  coe-Π : {I : Set k} {A : I -> Set i} {B : (i : I) -> A i -> Set j}
          {x y : I} {r : x ≡ y} {f : (a : A x) -> B x a}
        -> coe (λ i → (a : A i) -> B i a) r f
         ⇒ λ a → let aux = coe A (sym {a = x} r) a
                  in coe {I = Σ I A} (λ w → B (proj₁ w) (proj₂ w))
                         (sp r (sym' {A = A} (coh A _ a))) (f aux)

  coe-Prop : {I : Set k} {x y : I} {r : x ≡ y} {P : Prop j}
           -> coe {I = I} (λ i → Prop j) r P ⇒ P
  
  coe-refl : {I : Set i} (A : I -> Set j) {x : I} (p : x ≡ x) -> (a : A x)
           -> coe A p a ⇒ a

  coe-refl' : {I : Set i} {A : Set i} {i j : I} {p : i ≡ j} {a : A}
           -> coe {I = I} (λ _ → A) p a ⇒ a

{-# REWRITE HEq-Σ HEq-Π HEq-Lift coe-Σ coe-Π coe-Prop coe-refl coe-refl' #-}

postulate

  fromEq : {I : Set i} (A : I -> Set j) {x y : I} -> {p : x ≡ y}
         -> {a : A x} -> {a' : A y}
         → coe A p a ≡ a' -> HEq A p a a'

  toEq : {I : Set i} (A : I -> Set j) {x y : I} -> {p : x ≡ y}
         -> {a : A x} -> {a' : A y}
       -> HEq A p a a' -> coe A p a ≡ a'

  HEq-to-Eq : {I : Set i} {x y : I} {p : x ≡ y} {A : Set j} {a a' : A}
            -> HEq {I = I} (λ _ → A) p a a' -> a ≡ a'
  Eq-to-HEq : {I : Set i} {x y : I} {p : x ≡ y} {A : Set j} {a a' : A}
            -> a ≡ a' -> HEq {I = I} (λ _ → A) p a a'

module _ {A : Set i} {x : A} (C : (y : A) -> x ≡ y -> Set j)
         (d : C x (refl x))
         where

  J : {y : A} (p : x ≡ y) -> C y p
  J {y = y} p =
    coe {I = Σ A (λ y -> Lift (x ≡ y))} (λ w → C (proj₁ w) (unlift (proj₂ w)))
      {x , lift (refl x)} {y , lift p} (sp p tt) d

  J-refl : J {x} (refl x) ⇒ d
  J-refl = reduce

module _ {a : Level} {A : Set a} {b : Level} {B : Set b} (f : A → B) where

  cong : {x y : A} → x ≡ y → f x ≡ f y
  cong p = HEq-to-Eq {I = A} {p = p} {B} (refl f p)

module Eq-Reasoning {a : Level} (A : Set a) where

  ≡-to-HEq : {I : Set i} {x y : I} {p : x ≡ y} {a a' : A}
            -> a ≡ a' -> HEq {I = I} (λ _ → A) p a a'
  ≡-to-HEq = Eq-to-HEq {A = A}

  tr = trans {A = A}
  sy = sym {A = A}

  infix  3 _∎
  infixr 2 _≡⟨⟩_ step-≡ step-≡˘
  infix  1 begin_

  begin_ : ∀{x y : A} → x ≡ y → x ≡ y
  begin_ x≡y = x≡y

  _≡⟨⟩_ : ∀ (x {y} : A) → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  step-≡ : ∀ (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
  step-≡ _ y≡z x≡y = trans {A = A} x≡y y≡z

  step-≡˘ : ∀ (x {y z} : A) → y ≡ z → y ≡ x → x ≡ z
  step-≡˘ _ y≡z y≡x = trans {A = A} (sym {A = A} y≡x) y≡z

  _∎ : ∀ (x : A) → x ≡ x
  _∎ x = refl x

  syntax step-≡  x y≡z x≡y = x ≡⟨  x≡y ⟩ y≡z
  syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z
