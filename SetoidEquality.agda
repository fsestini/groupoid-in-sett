{-# OPTIONS --prop --rewriting --without-K #-}

open import Agda.Builtin.Equality renaming (_≡_ to _⇒_ ; refl to reduce)
open import Agda.Builtin.Equality.Rewrite
open import Lib

postulate

  Eq : (A : Set i) -> A -> A -> Prop i
  refl : (A : Set i) (a : A) -> Eq A a a

  HEq : {I : Set i} (A : I -> Set j) {i0 i1 : I} -> Eq I i0 i1 -> A i0 -> A i1 -> Prop j

  coe : {I : Set i} (A : I -> Set j) {i0 i1 : I} -> Eq I i0 i1 -> A i0 -> A i1

  coe-R : {I : Set i} (A : I -> Set j) {ix : I} {p : Eq I ix ix} {a : A ix}
        -> coe A p a ⇒ a

  coe-const : {I : Set i} {A : Set j} {i0 i1 : I} {p : Eq I i0 i1} {a : A}
            -> coe (λ _ -> A) p a ⇒ a

  Σ-Eq : {A : Set i} {B : A -> Set j} (p q : Σ A B)
       -> Eq (Σ A B) p q ⇒ Σp (Eq A (fst p) (fst q)) λ r → HEq B r (snd p) (snd q)
  Π-Eq : {A : Set i} {B : A -> Set j} (f g : (a : A) -> B a)
      -> Eq _ f g ⇒ ({a0 a1 : A} (r : Eq A a0 a1) -> HEq B r (f a0) (g a1))
  Prf-Eq : {P : Prop i} {p q : Prf P} -> Eq (Prf P) p q ⇒ ⊤
  Prop-Eq : {P Q : Prop i} -> Eq (Prop i) P Q ⇒ Σp' (P -> Q) (λ _ -> Q -> P)

  Prf-HEq : {I : Set i} {P : I -> Prop j} {i0 i1 : I} {p : Eq I i0 i1}
            {p0 : Prf (P i0)} {p1 : Prf (P i1)}
          -> HEq (λ i → Prf (P i)) p p0 p1 ⇒ ⊤

{-# REWRITE coe-R coe-const Σ-Eq Π-Eq Prf-Eq Prop-Eq Prf-HEq #-}

postulate

  Σ-HEq : {Γ : Set i} {A : Γ -> Set j} {B : (γ : Γ) -> A γ -> Set k}
            {γ₀ γ₁ : Γ} {p : Eq Γ γ₀ γ₁} {x : Σ (A γ₀) (B γ₀)} {y : Σ (A γ₁) (B γ₁)}
         -> HEq (λ γ → Σ (A γ) (B γ)) p x y
          ⇒ Σp (HEq A p (fst x) (fst y)) λ q → HEq {I = Σ Γ A} (λ { (γ , a) → B γ a}) (p ,p q) (snd x) (snd y)

  Π-HEq : {Γ : Set i} {A : Γ -> Set j} {B : (γ : Γ) -> A γ -> Set k}
            {γ₀ γ₁ : Γ} {p : Eq Γ γ₀ γ₁} {f₀ : (a : A γ₀) → B γ₀ a} {f₁ : (a : A γ₁) → B γ₁ a}
          -> HEq (λ γ → (a : A γ) -> B γ a) p f₀ f₁
           ⇒ ({a₀ : A γ₀} {a₁ : A γ₁} -> (q : HEq A p a₀ a₁)
             -> HEq {I = Σ Γ A} (λ w → B (fst w) (snd w)) (p ,p q) (f₀ a₀) (f₁ a₁))

  HEq-null : {I : Set i} {A : Set j} {i0 i1 : I} {p : Eq I i0 i1} {a0 a1 : A}
           -> HEq {I = I} (λ _ → A) p a0 a1 ⇒ Eq A a0 a1
  HEq-null' : {I : Set i} {A : I -> Set j} {ix : I} {p : Eq I ix ix} {a0 a1 : A ix}
           -> HEq {I = I} A p a0 a1 ⇒ Eq (A ix) a0 a1

{-# REWRITE Σ-HEq Π-HEq HEq-null HEq-null' #-}
-- {-# REWRITE Σ-HEq Π-HEq HEq-null #-} -- HEq-null' #-}

module _ {A : Set i} {B : Set j} {a0 a1 : A} (f : A -> B) (p : Eq A a0 a1) where

  postulate cong : Eq B (f a0) (f a1)
  -- cong = refl (A -> B) f p

module _ {A : Set i} {B : A -> Set j} {a a' : A} {p : Eq A a a'} where

  singl-contr : Eq (Σ A (λ a' -> Prf (Eq A a a'))) (a , prf (refl A a)) (a' , prf p)
  singl-contr = p ,p ttp

coeP : {I : Set i} (P : I -> Prop j) {i0 i1 : I} -> Eq I i0 i1 -> P i0 -> P i1
coeP P p x = unprf (coe (λ i → Prf (P i)) p (prf x))

module _ (A : Set i) where

  sym : {a a' : A} -> Eq A a a' -> Eq A a' a
  sym p = coeP (λ x → Eq A x _) p (refl A _)

  trans : {a a' a'' : A} -> Eq A a a' -> Eq A a' a'' -> Eq A a a''
  trans p q = coeP (λ x → Eq A _ x) q p

module _ {A : Set i} {x : A} (C : (y : A) -> Eq A x y -> Set j) (d : C x (refl A _)) where

  J : {y : A} (p : Eq A x y) -> C y p
  J {y} p =
    coe {I = Σ A (λ y -> Prf (Eq A x y))} (λ z → C (fst z) (unprf (snd z)))
        {x , prf (refl A _)} {y , prf p} (p ,p ttp) d

module _ {A : Set i} {x : A} (C : (y : A) -> Eq A x y -> Prop j) (d : C x (refl A _)) where

  JP : {y : A} (p : Eq A x y) -> C y p
  JP p = unprf (J (λ y q → Prf (C y q)) (prf d) p)

module _ {I : Set i} (A : I -> Set j) {i0 : I} where

  postulate coh : {i1 : I} -> (p : Eq I i0 i1) (a : A i0) -> HEq A p a (coe A p a)
  -- coh p a = JP {A = I} (λ i1 p → HEq A p a (coe A p a)) (refl _ a) p

module _ {I : Set i} (A : I -> Set j) {i0 i1 : I} {p : Eq I i0 i1}
         {a0 : A i0} {a1 : A i1} (q : HEq A p a0 a1) where

  module _ (C : (i : I) -> A i -> Set k) where

    coeH : C i0 a0 -> C i1 a1
    coeH c = coe {I = Σ I A} (λ x → C (fst x) (snd x)) (p ,p q) c

  module _ (C : (i : I) -> A i -> Prop k) where

    coeHP : C i0 a0 -> C i1 a1
    coeHP c = unprf (coeH (λ i x → Prf (C i x)) (prf c))

-- module _ {I : Set i} (A : I -> Set j) {i0 i1 : I} (p : Eq I i0 i1) where

--   to-Eq : {a0 : A i0} {a1 : A i1} -> HEq A p a0 a1 -> Eq (A i1) (coe A p a0) a1
--   to-Eq {a0} q =
--     let aux = JP (λ i p → {a : A i} -> HEq A p a0 a -> Eq (A i) (coe A p a0) a) (λ x → x) p
--     in aux q

--   from-Eq : {a0 : A i0} {a1 : A i1} -> Eq (A i1) (coe A p a0) a1 -> HEq A p a0 a1
--   from-Eq {a0} q =
--     let aux = JP (λ i p → {a : A i} -> Eq (A i) (coe A p a0) a -> HEq A p a0 a) (λ x → x) p
--     in aux q

-- module _ {Γ : Set i} (A : Γ -> Set j) {γ₀ : Γ} {a₀ : A γ₀}
--          (C : {γ₁ : Γ} {a₁ : A γ₁} (p : Eq Γ γ₀ γ₁) -> HEq A p a₀ a₁ -> Set k)
--          (d : C (refl Γ γ₀) (refl (A _) _))
--          where

--   J-on-HEq : {γ₁ : Γ} (p : Eq Γ γ₀ γ₁) {a₁ : A γ₁} (q : HEq A p a₀ a₁) -> C p q
--   J-on-HEq p q = J {A = Σ Γ A} (λ _ x → C (fstp x) (sndp x)) d (p ,p q)

-- module _ {I : Set i} (A : I -> Set j) {i0 : I} {a0 : A i0} where

--   module _ (C : (i : I) (p : Eq I i0 i) (a : A i) (q : HEq A p a0 a) -> Set k)
--            (d : C i0 (refl I _) a0 (refl (A i0) _)) where

--     JH : {i1 : I} (p : Eq I i0 i1) {a1 : A i1} (q : HEq A p a0 a1) -> C i1 p a1 q
--     JH p q = J-on-HEq A (λ p q → C _ p _ q) d p q

--   module _ (C : (i : I) (p : Eq I i0 i) (a : A i) (q : HEq A p a0 a) -> Prop k)
--            (d : C i0 (refl I _) a0 (refl (A i0) _)) where

--     JHP : {i1 : I} (p : Eq I i0 i1) {a1 : A i1} (q : HEq A p a0 a1) -> C i1 p a1 q
--     JHP p q = let aux = JH (λ i p a q → Prf (C i p a q)) (prf d) p q in unprf aux

-- module _ {I : Set i} (A : I -> Set j) {i0 i1 : I} (p : Eq I i0 i1) where

--   hsym : {a0 : A i0} {a1 : A i1} -> HEq A p a0 a1 -> HEq A (sym I p) a1 a0
--   hsym {a0} q = JHP A (λ i p a q → HEq A (sym I p) a a0) (refl (A i0) _) p q

-- module _ {I : Set i} (A : I -> Set j) {i0 i1 i2 : I} (p0 : Eq I i0 i1) (p1 : Eq I i1 i2) where

--   htrans : {a0 : A i0} {a1 : A i1} {a2 : A i2} -> HEq A p0 a0 a1 -> HEq A p1 a1 a2 -> HEq A (trans I p0 p1) a0 a2
--   htrans q0 q1 = JHP A (λ i p a q → HEq A (trans I p0 p) _ a) q0 p1 q1

-- module _ {A : Set i} {B : A -> Set j} (f : (a : A) -> B a) where

--   hcong : {a0 a1 : A} -> (p : Eq A a0 a1) -> HEq B p (f a0) (f a1)
--   hcong = refl _ f

-- postulate

--   coe-Σ : {I : Set k} {A : I -> Set i} {B : (i : I) -> A i -> Set j}
--           {i0 i1 : I} {p : Eq I i0 i1} {q : Σ (A i0) (B i0)}
--         -> coe (λ i → Σ (A i) (B i)) p q ⇒ (coe A p (fst q) , coe (λ x → B (fst x) (snd x)) (p ,p coh A p (fst q)) (snd q))

--   coe-Π : {I : Set k} {A : I -> Set i} {B : (i : I) -> A i -> Set j}
--           {i0 i1 : I} {p : Eq I i0 i1} {f : (a : A i0) -> B i0 a}
--         -> coe (λ i -> (a : A i) -> B i a) p f
--          ⇒ (λ a → coe (λ x → B (fst x) (snd x)) (p ,p hsym A (sym I p) (coh A (sym I p) a)) (f (coe A (sym I p) a)))

-- {-# REWRITE coe-Σ coe-Π #-}

_≡_ : {A : Set i} -> A -> A -> Prop i
_≡_ {A = A} = Eq A

module Eq-Reasoning {a : Level} (A : Set a) where

  infix  3 _∎
  infixr 2 _≡⟨⟩_ step-≡ step-≡˘
  infix  1 begin_

  sy = sym A
  tr = trans A
  infixl 4 _∙_
  _∙_ = tr

  begin_ : ∀{x y : A} → x ≡ y → x ≡ y
  begin_ x≡y = x≡y

  _≡⟨⟩_ : ∀ (x {y} : A) → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  step-≡ : ∀ (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
  step-≡ _ y≡z x≡y = trans A x≡y y≡z

  step-≡˘ : ∀ (x {y z} : A) → y ≡ z → y ≡ x → x ≡ z
  step-≡˘ _ y≡z y≡x = trans A (sym A y≡x) y≡z

  _∎ : ∀ (x : A) → x ≡ x
  _∎ = refl A

  syntax step-≡  x y≡z x≡y = x ≡⟨  x≡y ⟩ y≡z
  syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z
