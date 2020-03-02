{-# OPTIONS --prop --rewriting --without-K #-}

module DoubleEquality where

open import Data.Product
open import Agda.Builtin.Equality renaming (_≡_ to _⇒_) hiding (refl)
open import Agda.Builtin.Equality.Rewrite
open import Util

postulate
  _≡_ : {A : Set i} -> A -> A -> Prop i

  HEq : {Γ : Set i} (A : Γ -> Set j) {x y : Γ}
      -> x ≡ y -> A x -> A y -> Prop j
  
  refl : {A : Set i} (a : A) -> a ≡ a
  hrefl : {I : Set i} (A : I -> Set j) {x : I} (a : A x) -> HEq A (refl x) a a

  coe : {I : Set i} (A : I -> Set j) {x y : I} (p : x ≡ y) -> A x -> A y
  -- coh : {I : Set i} (A : I -> Set j) {x y : I} (p : x ≡ y) (a : A x)
  --     -> HEq A p a (coe A p a)

  from-coe : {I : Set i} (A : I -> Set j) {x y : I} {p : x ≡ y} {a : A x} {b : A y}
           -> (coe A p a ≡ b) ⇒ HEq A p a b

  Eq-Σ : {A : Set i} {B : A -> Set j} {p q : Σ A B}
       -> _≡_ {A = Σ A B} p q ⇒ ΣP (proj₁ p ≡ proj₁ q) λ r → HEq B r (proj₂ p) (proj₂ q)
  Eq-Π : {A : Set i} {B : A -> Set j} {f g : (a : A) -> B a}
       -> _≡_ {A = (a : A) -> B a} f g ⇒ ({a a' : A} (p : a ≡ a') -> HEq B p (f a) (g a'))
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

sym : (Γ : Set i) {x y : Γ} -> x ≡ y -> y ≡ x
sym Γ {x} {y} p = unlift (coe (λ z → Lift (z ≡ x)) p (lift (refl x)))

trans : (Γ : Set i) {x y z : Γ} -> x ≡ y -> y ≡ z -> x ≡ z
trans Γ {x} {y} {z} p q = unlift (coe (λ w → Lift (x ≡ w)) q (lift p))

hsym : {Γ : Set i} (A : Γ -> Set j) {γ₀ γ₁ : Γ} {p : γ₀ ≡ γ₁} {a₀ : A γ₀} {a₁ : A γ₁}
   -> HEq A p a₀ a₁ -> HEq A (sym Γ p) a₁ a₀
hsym {Γ = Γ} A {γ₀} {γ₁} {p} {a₀} {a₁} q = unlift (aux (sym Γ p))
  where
    eq : (γ₀ , a₀) ≡ (γ₁ , a₁)
    eq = sp p q
    aux = coe {I = Σ Γ A} (λ { (γ , a) → (p' : γ ≡ γ₀) -> Lift (HEq A p' a a₀) }) eq (λ p' → lift (hrefl A _))

HT : {Γ : Set i} (A : Γ -> Set j) {γ₀ γ₁ γ₂ : Γ} {p₀ : γ₀ ≡ γ₁} {p₁ : γ₁ ≡ γ₂}
     {a₀ : A γ₀} {a₁ : A γ₁} {a₂ : A γ₂}
   -> HEq A p₀ a₀ a₁ -> HEq A p₁ a₁ a₂ -> HEq A (trans Γ p₀ p₁) a₀ a₂
HT {Γ = Γ} A {γ₀} {γ₁} {γ₂} {p₀} {p₁} {a₀} {a₁} {a₂} q₀ q₁ = unlift (aux (trans Γ p₀ p₁))
  where
    aux = coe {I = Σ Γ A} (λ { (γ , a) → (p' : γ₀ ≡ γ) -> Lift (HEq A p' a₀ a) }) (sp p₁ q₁)
              (λ p' → lift q₀)

coh : {Γ : Set} (A : Γ -> Set)
    -> {x₀ x₁ : Γ} (p : x₀ ≡ x₁) (a : A x₀)
    -> HEq A p a (coe A p a)
coh {Γ} A {x₀} p a = unlift (aux p)
  where
    aux = coe {I = Γ} (λ γ → (p' : x₀ ≡ γ) -> Lift (HEq A p' a (coe A p' a))) p (λ p' → lift (hrefl A _))

postulate

  coe-Σ : {Γ : Set} {A : Γ -> Set} {B : (γ : Γ) -> A γ -> Set} {γ₀ γ₁ : Γ} {p : γ₀ ≡ γ₁} {q : Σ (A γ₀) (B γ₀)}
        -> coe (λ γ → Σ (A γ) (B γ)) p q ⇒ (coe A p (proj₁ q) , coe {I = Σ Γ A} (λ { (γ , a) → B γ a }) (sp p (coh A p (proj₁ q))) (proj₂ q))

  coe-Π : {Γ : Set} {A : Γ -> Set} {B : (γ : Γ) -> A γ -> Set} {γ₀ γ₁ : Γ} {p : γ₀ ≡ γ₁} {f : (a : A γ₀) -> B γ₀ a}
        -> coe (λ γ → (a : A γ) -> B γ a) p f ⇒ λ a → coe {I = Σ Γ A} (λ { (γ , a) → B γ a})
                                                          (sp p (hsym A (coh A (sym Γ p) a)))
                                                          (f (coe A (sym Γ p) a))

  HEq-Π-⇒ : {Γ : Set i} {A : Γ -> Set j} {B : (γ : Γ) -> A γ -> Set k}
            {γ₀ γ₁ : Γ} {p : γ₀ ≡ γ₁} {f₀ : (a : A γ₀) → B γ₀ a} {f₁ : (a : A γ₁) → B γ₁ a}
          -> HEq (λ γ → (a : A γ) -> B γ a) p f₀ f₁
           ⇒ ({a₀ : A γ₀} {a₁ : A γ₁} -> (q : HEq A p a₀ a₁) -> HEq {Γ = Σ Γ A} (λ x → B (proj₁ x) (proj₂ x)) (sp p q) (f₀ a₀) (f₁ a₁))

  HEq-Σ-⇒ : {Γ : Set i} {A : Γ -> Set j} {B : (γ : Γ) -> A γ -> Set k}
            {γ₀ γ₁ : Γ} {p : γ₀ ≡ γ₁} {x : Σ (A γ₀) (B γ₀)} {y : Σ (A γ₁) (B γ₁)}
         -> HEq (λ γ → Σ (A γ) (B γ)) p x y
          ⇒ ΣP (HEq A p (proj₁ x) (proj₁ y)) λ q → HEq {Γ = Σ Γ A} (λ { (γ , a) → B γ a}) (sp p q) (proj₂ x) (proj₂ y)

  HEq-Prf-⇒ : {Γ : Set i} {P : Γ -> Prop j} {γ₀ γ₁ : Γ} {p : γ₀ ≡ γ₁} {x : _} {y : _}
            -> HEq (λ γ → Lift (P γ)) p x y ⇒ ⊤

  HEq-Prop-⇒ : {Γ : Set i} {γ₀ γ₁ : Γ} {p : γ₀ ≡ γ₁} {P Q : Prop j}
             -> HEq {Γ = Γ} (λ _ -> Prop j) p P Q ⇒ ΣP' (P -> Q) λ _ → Q -> P

{-# REWRITE coe-Σ coe-Π HEq-Π-⇒ HEq-Σ-⇒ HEq-Prf-⇒ HEq-Prop-⇒ #-}

module _ {A : Set i} {B : A -> Set j} (f : (a : A) -> B a) where

  dcong : {x y : A} -> (p : x ≡ y) -> HEq B p (f x) (f y)
  dcong = refl f

module _ {A : Set i} {B : Set j} (f : A -> B) where

  cong : {x y : A} -> (p : x ≡ y) -> f x ≡ f y
  cong p = {!dcong f p!}
