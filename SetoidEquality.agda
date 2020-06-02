{-# OPTIONS --prop --rewriting --without-K #-}

open import Data.Product
open import Agda.Builtin.Equality renaming (_≡_ to _⇒_ ; refl to reduce)
open import Agda.Builtin.Equality.Rewrite
open import Util

postulate
  Eq : (Γ : Set i) -> Γ -> Γ -> Prop i
  HEq : {Γ : Set i} (A : Γ -> Set j) {x y : Γ}
      -> Eq Γ x y -> A x -> A y -> Prop j
  
  coe : {Γ : Set i} (A : Γ -> Set j)
        {x₀ x₁ : Γ} -> Eq Γ x₀ x₁ -> A x₀ -> A x₁

  coe-R : {Γ : Set} {A : Γ -> Set} {γ : Γ} {p : Eq Γ γ γ} {x : A γ} -> coe A p x ⇒ x

  coe-const : {Γ : Set i} {A : Set j} {x y : Γ} {p : Eq Γ x y} {a : A}
            -> coe {Γ = Γ} (λ _ → A) p a ⇒ a

  R  : (Γ : Set i) (x : Γ) -> Eq Γ x x
  HR : {Γ : Set i} (A : Γ -> Set j) {x : Γ} -> (a : A x) -> HEq A (R Γ x) a a

  Eq-⊤-⇒ : ∀{x y} -> Eq (𝟙 {i}) x y ⇒ ⊤
  Eq-Σ-⇒ : {A : Set i} {B : A -> Set j} {p q : Σ A B}
         → Eq (Σ A B) p q ⇒ ΣP (Eq A (proj₁ p) (proj₁ q)) λ r → HEq B r (proj₂ p) (proj₂ q)

{-# REWRITE Eq-⊤-⇒ Eq-Σ-⇒ coe-R coe-const #-}

S : (Γ : Set i) {x y : Γ} -> Eq Γ x y -> Eq Γ y x
S Γ {x} {y} p = unlift (coe (λ z → Lift (Eq Γ z x)) p (lift (R Γ _)))

T : (Γ : Set i) {x y z : Γ} -> Eq Γ x y -> Eq Γ y z -> Eq Γ x z
T Γ {x} {y} {z} p q = unlift (coe (λ w → Lift (Eq Γ x w)) q (lift p))

HS : {Γ : Set i} (A : Γ -> Set j) {γ₀ γ₁ : Γ} {p : Eq Γ γ₀ γ₁} {a₀ : A γ₀} {a₁ : A γ₁}
   -> HEq A p a₀ a₁ -> HEq A (S Γ p) a₁ a₀
HS {Γ = Γ} A {γ₀} {γ₁} {p} {a₀} {a₁} q = unlift (aux (S Γ p))
  where
    eq : Eq (Σ Γ A) (γ₀ , a₀) (γ₁ , a₁)
    eq = sp p q
    aux = coe {Γ = Σ Γ A} (λ { (γ , a) → (p' : Eq Γ γ γ₀) -> Lift (HEq A p' a a₀) }) eq (λ p' → lift (HR A _))

coh : {Γ : Set} (A : Γ -> Set)
    -> {x₀ x₁ : Γ} (p : Eq Γ x₀ x₁) (a : A x₀)
    -> HEq A p a (coe A p a)
coh {Γ} A {x₀} p a = unlift (aux p)
  where
    aux = coe {Γ = Γ} (λ γ → (p' : Eq Γ x₀ γ) -> Lift (HEq A p' a (coe A p' a))) p (λ p' → lift (HR A _))

HT : {Γ : Set i} (A : Γ -> Set j) {γ₀ γ₁ γ₂ : Γ} {p₀ : Eq Γ γ₀ γ₁} {p₁ : Eq Γ γ₁ γ₂}
     {a₀ : A γ₀} {a₁ : A γ₁} {a₂ : A γ₂}
   -> HEq A p₀ a₀ a₁ -> HEq A p₁ a₁ a₂ -> HEq A (T Γ p₀ p₁) a₀ a₂
HT {Γ = Γ} A {γ₀} {γ₁} {γ₂} {p₀} {p₁} {a₀} {a₁} {a₂} q₀ q₁ = unlift (aux (T Γ p₀ p₁))
  where
    aux = coe {Γ = Σ Γ A} (λ { (γ , a) → (p' : Eq Γ γ₀ γ) -> Lift (HEq A p' a₀ a) }) (sp p₁ q₁)
              (λ p' → lift q₀)

postulate
  coe-Σ : {Γ : Set} {A : Γ -> Set} {B : (γ : Γ) -> A γ -> Set} {γ₀ γ₁ : Γ} {p : Eq Γ γ₀ γ₁} {q : Σ (A γ₀) (B γ₀)}
        -> coe (λ γ → Σ (A γ) (B γ)) p q ⇒ (coe A p (proj₁ q) , coe {Γ = Σ Γ A} (λ { (γ , a) → B γ a }) (sp p (coh A p (proj₁ q))) (proj₂ q))

  coe-Π : {Γ : Set} {A : Γ -> Set} {B : (γ : Γ) -> A γ -> Set} {γ₀ γ₁ : Γ} {p : Eq Γ γ₀ γ₁} {f : (a : A γ₀) -> B γ₀ a}
        -> coe (λ γ → (a : A γ) -> B γ a) p f ⇒ λ a → coe {Γ = Σ Γ A} (λ { (γ , a) → B γ a}) (sp p (HS A (coh A _ _))) (f (coe A (S Γ p) a))
  
  HEq-Π-⇒ : {Γ : Set i} {A : Γ -> Set j} {B : (γ : Γ) -> A γ -> Set k}
            {γ₀ γ₁ : Γ} {p : Eq Γ γ₀ γ₁} {f₀ : (a : A γ₀) → B γ₀ a} {f₁ : (a : A γ₁) → B γ₁ a}
          -> HEq (λ γ → (a : A γ) -> B γ a) p f₀ f₁
           ⇒ ({a₀ : A γ₀} {a₁ : A γ₁} -> (q : HEq A p a₀ a₁) -> HEq {Γ = Σ Γ A} (λ x → B (proj₁ x) (proj₂ x)) (sp p q) (f₀ a₀) (f₁ a₁))

  HEq-Σ-⇒ : {Γ : Set i} {A : Γ -> Set j} {B : (γ : Γ) -> A γ -> Set k}
            {γ₀ γ₁ : Γ} {p : Eq Γ γ₀ γ₁} {x : Σ (A γ₀) (B γ₀)} {y : Σ (A γ₁) (B γ₁)}
         -> HEq (λ γ → Σ (A γ) (B γ)) p x y
          ⇒ ΣP (HEq A p (proj₁ x) (proj₁ y)) λ q → HEq {Γ = Σ Γ A} (λ { (γ , a) → B γ a}) (sp p q) (proj₂ x) (proj₂ y)

  HEq-Prf-⇒ : {Γ : Set i} {P : Γ -> Prop j} {γ₀ γ₁ : Γ} {p : Eq Γ γ₀ γ₁} {x : _} {y : _}
            -> HEq (λ γ → Lift (P γ)) p x y ⇒ ⊤

  HEq-Prop-⇒ : {Γ : Set i} {γ₀ γ₁ : Γ} {p : Eq Γ γ₀ γ₁} {P Q : Prop j}
             -> HEq {Γ = Γ} (λ _ -> Prop j) p P Q ⇒ ΣP' (P -> Q) λ _ → Q -> P

{-# REWRITE coe-Σ coe-Π HEq-Π-⇒ HEq-Σ-⇒ HEq-Prf-⇒ HEq-Prop-⇒ #-}

-- Id : (A : Set i) -> A -> A -> Prop i
-- Id A = HEq {Γ = 𝟙 {lzero}} (λ _ → A) tt

Id : {I : Set i} (A : I -> Set j) {x : I} -> A x -> A x -> Prop j
Id {I = I} A a b = HEq A (R I _) a b

-- foo : {I : Set i} (A : Set j) {x y : I} {a : A} {p : Eq I x y}
--     -> HEq {Γ = I} (λ _ -> A) p a a ⇒ Id {I = I} (λ _ -> A) {x} a a
-- foo A = reduce

-- Id' : (A : Set i) -> A -> A -> Prop (lsuc i)
-- Id' {i = i} A a b = {Γ : Set i} {x y : Γ} {p : Eq Γ x y} -> HEq {Γ = Γ} (λ _ → A) p a b

-- _≡_ : {A : Set i} -> A -> A -> Prop i
-- _≡_ {A = A} = Id A

-- refl : (A : Set i) {a : A} -> a ≡ a
-- refl A = HR (λ _ → A) _

-- sym : (A : Set i) {a a' : A} -> a ≡ a' -> a' ≡ a
-- sym A p = HS (λ _ -> A) p

-- trans : (A : Set i) {a a' a'' : A} -> a ≡ a' -> a' ≡ a'' -> a ≡ a''
-- trans A p q = HT (λ _ -> A) p q

-- Het : {A : Set i} (B : A -> Set j) {x y : A}
--     -> x ≡ y -> B x -> B y -> Prop j
-- Het {A = A} B p = HEq {Γ = Σ (𝟙 {lzero}) (λ _ → A)} (λ x → B (proj₂ x)) (sp tt p)

-- module _ {A : Set i} (B : A -> Set j) where

--   hrefl : {a : A} {b : B a} -> Het B (refl A) b b
--   hrefl = HR (λ x → B (proj₂ x)) _

--   hsym : {γ₀ γ₁ : A} {p : γ₀ ≡ γ₁} {a₀ : B γ₀} {a₁ : B γ₁}
--        -> Het B p a₀ a₁ -> Het B (sym A p) a₁ a₀
--   hsym = HS (λ x -> B (proj₂ x))

--   htrans : {γ₀ γ₁ γ₂ : A} {p₀ : γ₀ ≡ γ₁} {p₁ : γ₁ ≡ γ₂}
--            {a₀ : B γ₀} {a₁ : B γ₁} {a₂ : B γ₂}
--          -> Het B p₀ a₀ a₁ -> Het B p₁ a₁ a₂ -> Het B (trans A p₀ p₁) a₀ a₂
--   htrans = HT (λ x -> B (proj₂ x))

-- module _ (A : Set j) {a b : A} where

--   to-Id : Eq A a b -> a ≡ b
--   to-Id p = unlift aux
--     where
--       aux = coe (λ x → Lift (HEq (λ _ → A) tt a x)) p (lift (HR (λ _ -> A) _))

-- postulate
--   coe-Prf : {Γ : Set i} {P : Γ -> Prop j} {γ₀ γ₁ : Γ} {p : Eq Γ γ₀ γ₁} {x : P γ₀}
--           -> let aux : Id (Prop _) (P γ₀) (P γ₁)
--                  aux = refl (Γ -> Prop j) {P} (to-Id Γ p)
--              in coe (λ γ → Lift (P γ)) p (lift x) ⇒ lift (fst' aux x)

-- {-# REWRITE coe-Prf #-}

module _ {Γ : Set i} {γ : Γ} (C : {γ' : Γ} -> Eq Γ γ γ' -> Set j)
         (d : C (R Γ γ))
  where

  J-on-Eq : {γ' : Γ} (p : Eq Γ γ γ') -> C p
  J-on-Eq p = coe {Γ = Γ} (λ γ' -> (p : Eq Γ γ γ') -> C p) p (λ _ → d) p

module _ {Γ : Set i} (A : Γ -> Set j) {γ₀ : Γ} {a₀ : A γ₀}
         (C : {γ₁ : Γ} {a₁ : A γ₁} (p : Eq Γ γ₀ γ₁) -> HEq A p a₀ a₁ -> Set k)
         (d : C (R Γ γ₀) (HR A a₀))
         where

  J-on-HEq : {γ₁ : Γ} (p : Eq Γ γ₀ γ₁) {a₁ : A γ₁} (q : HEq A p a₀ a₁) -> C p q
  J-on-HEq p q = J-on-Eq {Γ = Σ Γ A} (λ { (sp p q) → C p q}) d (sp p q)

-- module _ {A : Set i} {γ : A} (C : (γ' : A) -> γ ≡ γ' -> Set j)
--          (d : C γ (refl A))
--   where

--   J : {γ' : A} (p : γ ≡ γ') -> C γ' p
--   J = J-on-HEq {Γ = 𝟙 {lzero}} (λ _ → A) (λ _ → C _) d (R (𝟙 {lzero}) _)

-- module _ {A : Set i} (B : A -> Set j) where

--   transp : {x y : A} -> x ≡ y -> B x -> B y
--   transp p x = J (λ y _ → B y) x p

module _ {Γ : Set i} {Γ' : Set j} (A : Set k)
         {γ₀ γ₁ : Γ} {p : Eq Γ γ₀ γ₁}
         {γ₀' γ₁' : Γ'} {p' : Eq Γ' γ₀' γ₁'} {a₀ : A} where

  ctx-irrel : {a₁ : A} -> HEq {Γ = Γ} (λ _ -> A) p a₀ a₁ -> HEq {Γ = Γ'} (λ _ -> A) p' a₀ a₁
  ctx-irrel q = unlift aux
    where
      aux = J-on-HEq (λ _ -> A) (λ { {a₁ = a₁} p q → Lift (HEq {Γ = Γ'} (λ _ -> A) p' a₀ a₁) })
              (J-on-Eq {Γ = Γ'} (λ p' → Lift (HEq (λ _ → A) p' a₀ a₀)) (lift (HR (λ _ → A) a₀)) p') p q

-- module _ {A : Set i} {B : Set j} (f : A -> B) where

--   private
--     cong' : {a₀ a₁ : A} (q : Id A a₀ a₁)
--          → HEq {Γ = Σ (𝟙 {lzero}) (λ _ -> A)} (λ { _ → B}) (sp tt q) (f a₀) (f a₁)
--     cong' q = refl (A -> B) {f} q

--   cong : {a₀ a₁ : A} (q : Id A a₀ a₁) -> Id B (f a₀) (f a₁)
--   cong q = ctx-irrel B (cong' q) 

-- module Eq-Reasoning {a : Level} (A : Set a) where

--   infix  3 _∎
--   infixr 2 _≡⟨⟩_ step-≡ step-≡˘
--   infix  1 begin_

--   sy = sym A
--   tr = trans A
--   infixl 4 _∙_
--   _∙_ = tr

--   begin_ : ∀{x y : A} → x ≡ y → x ≡ y
--   begin_ x≡y = x≡y

--   _≡⟨⟩_ : ∀ (x {y} : A) → x ≡ y → x ≡ y
--   _ ≡⟨⟩ x≡y = x≡y

--   step-≡ : ∀ (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
--   step-≡ _ y≡z x≡y = trans A x≡y y≡z

--   step-≡˘ : ∀ (x {y z} : A) → y ≡ z → y ≡ x → x ≡ z
--   step-≡˘ _ y≡z y≡x = trans A (sym A y≡x) y≡z

--   _∎ : ∀ (x : A) → x ≡ x
--   _∎ x = refl A

--   syntax step-≡  x y≡z x≡y = x ≡⟨  x≡y ⟩ y≡z
--   syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z
