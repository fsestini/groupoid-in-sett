{-# OPTIONS --prop --rewriting --without-K #-}

module Equality where

open import Agda.Builtin.Equality renaming (_≡_ to _⇒_ ; refl to reduce)
open import Agda.Builtin.Equality.Rewrite
open import Data.Product
open import Util

private
  postulate
    R~ : (P : Prop i) -> P -> P -> Prop i
    RR~ : {P : Prop i} (p : P) -> R~ P p p

postulate
  _≡_ : {A : Set i} -> A -> A -> Prop i

  refl : {A : Set i} (a : A) -> a ≡ a
  sym : {A : Set i} {a a' : A} -> a ≡ a' -> a' ≡ a
  trans : {A : Set i} {a a' a'' : A} -> a ≡ a' -> a' ≡ a'' -> a ≡ a''

  coe : {I : Set i} (A : I -> Set j) {x y : I} (p : x ≡ y) -> A x -> A y

  Eq-Σ : {A : Set i} {B : A -> Set j} {p q : Σ A B}
       -> _≡_ {A = Σ A B} p q ⇒ ΣP (proj₁ p ≡ proj₁ q) λ r → coe B r (proj₂ p) ≡ proj₂ q
  Eq-Π : {A : Set i} {B : A -> Set j} {f g : (a : A) -> B a}
       -> _≡_ {A = (a : A) -> B a} f g ⇒ ({a a' : A} (p : a ≡ a') -> coe B p (f a) ≡ g a')
  Eq-Prop : {P Q : Prop i} -> _≡_ {A = Prop i} P Q ⇒ ΣP' (P -> Q) λ _ -> Q -> P
  Eq-Lift : {P : Prop i} {p q : P}
          -> _≡_ {A = Lift P} (lift p) (lift q) ⇒ ⊤

{-# REWRITE Eq-Σ Eq-Π Eq-Prop Eq-Lift #-}

postulate

  coe-refl : {I : Set i} (A : I -> Set j) {x : I} (p : x ≡ x) -> (a : A x)
           -> coe {I = I} A p a ⇒ a

  coe-refl' : {I : Set i} {A : Set j} {i j : I} {p : i ≡ j} {a : A}
           -> coe {I = I} (λ _ → A) p a ⇒ a

{-# REWRITE coe-refl coe-refl' #-}

module _ {A : Set i} {x : A} (C : (y : A) -> x ≡ y -> Set j)
         (d : C x (refl x))
         where

  J : {y : A} (p : x ≡ y) -> C y p
  J {y = y} p =
    coe {I = Σ A (λ y -> Lift (x ≡ y))} (λ w → C (proj₁ w) (unlift (proj₂ w)))
      {x , lift (refl x)} {y , lift p} (sp p tt) d

  J-refl : J {x} (refl x) ⇒ d
  J-refl = reduce

module _ {A : Set i} {x : A} (C : (y : A) -> x ≡ y -> Prop j)
         (d : C x (refl x))
         where

  private
    C' : (y : A) -> x ≡ y -> Set j 
    C' y p = Lift (C y p)

  J-Prop : {y : A} (p : x ≡ y) -> C y p
  J-Prop p = let aux = J C' (lift d) p in unlift aux

  J-refl-Prop : R~ _ (J-Prop (refl x)) d
  J-refl-Prop = RR~ _

module _ {I : Set i} (A : I -> Set j)
         {x y : I} (p : x ≡ y) (a : A x) where

  coe∙coe : ∀{z} (q : y ≡ z) -> coe A q (coe A p a) ≡ coe A (trans {A = I} p q) a
  coe∙coe q =
    J-Prop {A = I} {y} (λ _ q' → coe A q' (coe A p a) ≡ coe A (trans {A = I} p q') a)
      (refl (coe A _ a)) q

postulate

  coe-Σ : {I : Set k} {A : I -> Set i} {B : (i : I) -> A i -> Set j}
          {x y : I} {r : x ≡ y} {p : Σ (A x) (B x)}
        -> coe (λ i → Σ (A i) (B i)) r p
         ⇒ ( coe A r (proj₁ p)
           , coe {I = Σ I A} (λ w → B (proj₁ w) (proj₂ w))
                 (sp r (refl (coe A _ (proj₁ p))))
                 (proj₂ p))

  coe-Π : {I : Set k} {A : I -> Set i} {B : (i : I) -> A i -> Set j}
          {x y : I} {r : x ≡ y} {f : (a : A x) -> B x a}
        -> coe (λ i → (a : A i) -> B i a) r f
         ⇒ λ a → let aux = coe A (sym {a = x} r) a
                  in coe {I = Σ I A} (λ w → B (proj₁ w) (proj₂ w))
                         (sp r (coe∙coe A (sym {a = x} r) a r))
                         (f aux)

{-# REWRITE coe-Σ coe-Π #-}

module _ {a : Level} {A : Set a} {b : Level} {B : Set b} (f : A → B) where

  cong : {x y : A} → x ≡ y → f x ≡ f y
  cong {x} {y} p = refl f p

module _ {A : Set i} {B : A -> Set j} where

  module _ {p : Σ A B} where

    private
      test : p ≡ p
      test = sp (refl (proj₁ p)) (refl (proj₂ p))

  module _ {f : (a : A) -> B a} where

    private
      test : f ≡ f
      test = λ p → refl f p

HEq : {I : Set i} (A : I -> Set j) {x y : I} -> x ≡ y -> A x -> A y -> Prop j
HEq A p a a' = coe A p a ≡ a'

module Eq-Reasoning {a : Level} (A : Set a) where

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
