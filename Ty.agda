{-# OPTIONS --prop --rewriting --without-K --allow-unsolved-metas #-}

module Ty where

open import Agda.Builtin.Equality renaming (_≡_ to _⇒_ ; refl to reduce)
open import Agda.Builtin.Equality.Rewrite

open import Data.Product
open import Util
open import Equality
open import Groupoid

record Ty (j : Level) {i} (Γ : Con i) : Set (i ⊔ lsuc j) where
  no-eta-equality
  field
    ∣_∣* : ∣ Γ ∣ -> Groupoid j
    subst* : ∀{x y} -> Hom Γ x y -> ∣_∣* x ⟶ ∣_∣* y

    refl*0 : ∀{γ} x -> f0 (subst* (R Γ γ)) x ≡ x
    refl*1 : ∀{γ x y} (p : Hom (∣_∣* γ) x y)
           → HEq (λ w → Hom ∣ γ ∣* (proj₁ w) (proj₂ w))
                 (sp (refl*0 x) (refl*0 y))
                 (f1 (subst* (R Γ γ)) p) p
    trans*0 : ∀{x y z} (p : Hom Γ x y) (q : Hom Γ y z) a
            -> f0 (subst* (T Γ p q)) a ≡ f0 (subst* q) (f0 (subst* p) a)
    trans*1 : ∀{x y z} (p : Hom Γ x y) (q : Hom Γ y z) {a b} (r : Hom ∣ x ∣* a b)
            -> HEq (λ w → Hom ∣ z ∣* (proj₁ w) (proj₂ w))
                   (sp (trans*0 _ _ _) (trans*0 _ _ _))
                   (f1 (subst* (T Γ p q)) {a} {b} r) (f1 (subst* q) (f1 (subst* p) r))
open Ty public

postulate
  Ty≡ : {i : Level} {Γ : Con i} {A B : Ty j Γ}
      -> _≡_ {A = Ty j Γ} A B
       ⇒ ΣP (∣ A ∣* ≡ ∣ B ∣*) λ eq1
       → HEq {I = ∣ Γ ∣ -> Groupoid _}
             (λ X → ∀{x y} -> Hom Γ x y -> X x ⟶ X y) eq1
             (subst* A) (subst* B)
{-# REWRITE Ty≡ #-}

module _ {Γ : Con i} (A : Ty j Γ) where

  IxHom : ∀{γ γ'} -> (p : Hom Γ γ γ') -> ∣ ∣ A ∣* γ ∣ -> ∣ ∣ A ∣* γ' ∣ -> Set j
  IxHom {γ} {γ'} p x y = Hom (∣ A ∣* γ') (f0 (subst* A p) x) y

  transp-IxHom : ∀{γ γ' x y} {p q : Hom Γ γ γ'} -> p ≡ q -> IxHom p x y -> IxHom q x y
  transp-IxHom r = coe (λ z -> IxHom z _ _) r

  IxR : ∀{γ} x -> IxHom (R Γ γ) x x
  IxR x =
    coe (λ z → Hom (∣ A ∣* _) z _) (sym {A = ∣ ∣ A ∣* _ ∣} (refl*0 A x))
      (R (∣ A ∣* _) x)

  IxS : ∀{γ γ' x y} {p : Hom Γ γ γ'} -> IxHom p x y -> IxHom (S Γ p) y x
  IxS {γ} {γ'} {x} {y} {p} q =
    let open Eq-Reasoning (∣ ∣ A ∣* _ ∣)
        eq = begin
          _ ≡⟨ sy (trans*0 A p (S Γ p) x) ⟩
          _ ≡⟨ cong (λ z -> f0 (subst* A z) x) (inv1 Γ {p = p}) ⟩
          _ ≡⟨ refl*0 A x ⟩
          _ ∎
    in coe (Hom (∣ A ∣* γ) _) eq (f1 (subst* A (S Γ p)) (S (∣ A ∣* γ') q))

  postulate
    IxT : ∀{x y z x' y' z'} {p : Hom Γ x y} {q : Hom Γ y z}
          -> IxHom p x' y' -> IxHom q y' z' -> IxHom (T Γ p q) x' z'
    -- IxT {x} {y} {z} {x'} {p = p} {q} p' q' =
    --   T (∣ A ∣* z)
    --   {!!} -- (coe (λ z → Hom (∣ A ∣* _) z (f0 (subst* A q) _))
    --   --   {!!} (f1 (subst* A q) p'))
    --   q'
    -- where
    --   -- actual definition crashes Agda for some reason :/
    --   postulate eq : f0 (subst* A q) (f0 (subst* A p) x') ≡ f0 (subst* A (T Γ p q)) x'
    --   --   let eq : f0 (subst* A q) (f0 (subst* A p) x') ≡ f0 (subst* A (T Γ p q)) x'
    --   --       eq = sym {A = ∣ ∣ A ∣* z ∣} (trans*0 A p q x')

  id1* : ∀{γ γ' x y} {p : Hom Γ γ γ'} (q : IxHom p x y)
       -> HEq (λ z -> IxHom z x y) (id1 Γ) (IxT q (IxR y)) q
  id1* {γ = γ} {γ'} {x} {y} q = {!!}
    -- {!id1 (∣ A ∣* _) {p = q}!}
    where
      aux : HEq (λ z -> IxHom z x y) (id1 Γ) (IxT q (IxR y)) (T (∣ A ∣* γ') q (R (∣ A ∣* γ') y))
      aux = {!refl*1 A q!}

  id2* : ∀{γ γ' x y} {p : Hom Γ γ γ'} (q : IxHom p x y)
         -> HEq (λ z -> IxHom z x y) (id2 Γ) (IxT (IxR _) q) q
  id2* = {!!}

  assoc* : ∀{γ₀ γ₀' x₀ y₀} {p1 : Hom Γ γ₀ γ₀'} (q1 : IxHom p1 x₀ y₀)
              {γ₁' y₁} {p2 : Hom Γ γ₀' γ₁'} (q2 : IxHom p2 y₀ y₁)
              {γ₂' y₂} {p3 : Hom Γ γ₁' γ₂'} (q3 : IxHom p3 y₁ y₂)
           -> HEq (λ z -> IxHom z _ _) (assoc Γ) (IxT q1 (IxT q2 q3)) (IxT (IxT q1 q2) q3)
  assoc* = {!!}

  inv1* : ∀{γ₀ γ₁ x y} {p : Hom Γ γ₀ γ₁} (q : IxHom p x y)
        -> HEq (λ z -> IxHom z _ _) (inv1 Γ {p = p}) (IxT q (IxS q)) (IxR x)
  inv1* = {!!}

  inv2* : ∀{γ₀ γ₁ x y} {p : Hom Γ γ₀ γ₁} (q : IxHom p x y)
        -> HEq (λ z -> IxHom z _ _) (inv2 Γ {p = p}) (IxT (IxS q) q) (IxR y)
  inv2* = {!!}

module _ {Γ : Con i} (A : Ty j Γ) {γ γ' γ'' a b}
         (p : Hom Γ γ γ') {p' : Hom Γ γ'' γ}
         (q : IxHom A p' a b) where

  subst*-Ix1 : IxHom A p (f0 (subst* A p') a) (f0 (subst* A p) b)
  subst*-Ix1 = f1 (subst* A p) q

module _ {Γ : Con i} (A : Ty j Γ)
         {γ₀ γ₁ γ₀' γ₁'} {p₀ : Hom Γ γ₀ γ₁} {p₁ : Hom Γ γ₀' γ₁'}
         {k₀ : Hom Γ γ₀ γ₀'} {k₁ : Hom Γ γ₁ γ₁'}
         {a₀ a₁}
         where

  subst*-eq : HomEq Γ k₀ k₁ p₀ p₁
            → IxHom A k₀ a₀ a₁
            → IxHom A _
                      (f0 (subst* A p₀) a₀)
                      (f0 (subst* A p₁) a₁)
  subst*-eq p-eq a-morph = IxT A m (subst*-Ix1 A p₁ a-morph)
    where
      open Eq-Reasoning (∣ ∣ A ∣* _ ∣)
      aux-eq : T Γ p₀ (T Γ k₁ (S Γ p₁)) ≡ k₀
      aux-eq = {!!}
      aux-eq' = tr (sy (trans*0 A _ _ a₀)) (cong (λ z → f0 (subst* A z) a₀) aux-eq)
      m = coe (λ z → Hom (∣ A ∣* _) z (f0 (subst* A k₀) a₀))
              (sy aux-eq') (R (∣ A ∣* _) (f0 (subst* A k₀) a₀))

module _ {Γ : Con i} (A : Ty j Γ) {γ a₀ a₁} where

  Hom-to-IxHom : Hom (∣ A ∣* γ) a₀ a₁ -> IxHom A (R Γ _) a₀ a₁
  Hom-to-IxHom p =
    coe (λ z → Hom (∣ A ∣* _) z _) (sym {A = ∣ ∣ A ∣* _ ∣} (refl*0 A a₀)) p

module _ {Γ : Con i} (A : Ty j Γ) where

  IxHomEq : ∀{γ γ' γ'' γ''' x y x' y'}
              {p₀ : Hom Γ γ γ'} {p₁ : Hom Γ γ'' γ'''}
              {p₂ : Hom Γ _ _} {p₃ : Hom Γ _ _}
           -> HomEq Γ p₂ p₃ p₀ p₁
           -> (k₀ : IxHom A p₂ x x')
           -> (k₁ : IxHom A p₃ y y')
           -> IxHom A p₀ x y -> IxHom A p₁ x' y'
           -> Prop _
  IxHomEq r k₀ k₁ q₀ q₁ =
    -- HEq (λ z → IxHom A z _ _) r (IxT A (IxS A k₀) (IxT A q₀ k₁)) q₁
    coe (λ z -> IxHom A z _ _) r (IxT A (IxS A k₀) (IxT A q₀ k₁)) ≡ q₁

  module _
           {γ₀ γ₁ γ₂ γ₃ x₀ y₀ x₁ y₁}
           {p₀ : Hom Γ γ₀ γ₁} {p₁ : Hom Γ γ₂ γ₃}
           {p₂ : Hom Γ _ _} {p₃ : Hom Γ _ _}
           {r : HomEq Γ p₂ p₃ p₀ p₁}
           {k₀ : IxHom A p₂ x₀ x₁}
           {k₁ : IxHom A p₃ y₀ y₁}
           {q₀ : IxHom A p₀ x₀ y₀}
           {q₁ : IxHom A p₁ x₁ y₁}

           {γ₀' γ₁' γ₂' γ₃' x₀' y₀' x₁' y₁'}
           {p₀' : Hom Γ γ₀' γ₁'} {p₁' : Hom Γ γ₂' γ₃'}
           {p₂' : Hom Γ _ _} {p₃' : Hom Γ _ _}
           {r' : HomEq Γ p₂' p₃' p₀' p₁'}
           {k₀' : IxHom A p₂' x₀' x₁'}
           {k₁' : IxHom A p₃' y₀' y₁'}
           {q₀' : IxHom A p₀' x₀' y₀'}
           {q₁' : IxHom A p₁' x₁' y₁'}

           {j₀ j₁ j₂ j₃}
           {k₀'' : IxHom A j₀ x₁ x₁'}
           {k₀''' : IxHom A j₁ x₀ x₀'}
           {k₁'' : IxHom A j₂ y₁ y₁'}
           {k₁''' : IxHom A j₃ y₀ y₀'}
           {r-right : HomEq Γ _ _ p₁ p₁'}
           {r-top : HomEq Γ _ _ p₂ p₂'}
           {r-bottom : HomEq Γ p₃ p₃' _ _}
           {r-left : HomEq Γ _ _ p₀ p₀'}

           (eq-top : IxHomEq r-top k₀''' k₀'' k₀ k₀')
           (eq-bottom : IxHomEq r-bottom k₁ k₁' k₁''' k₁'')
           (eq-left : IxHomEq r-left k₀''' k₁''' q₀ q₀')
           (eq-right : IxHomEq r-right k₀'' k₁'' q₁ q₁')
           where

    IxHomEq-≡ : IxHomEq r k₀ k₁ q₀ q₁ ≡ IxHomEq r' k₀' k₁' q₀' q₁'
    IxHomEq-≡ = {!!}

module _ (A : Ty j Γ) {γ₀ γ₁ γ₀' γ₁' a₀ a₁}
         {p : Hom Γ γ₀ γ₁} {p₀ : Hom Γ γ₀' γ₀} {p₁ : Hom Γ γ₁' γ₁}
         {k₀ : Hom Γ γ₀' γ₁'} {k₁ : Hom Γ γ₀ γ₁}
         {j₀ : IxHom A k₀ a₀ a₁} {j₁ : IxHom A k₁ (f0 (subst* A p₀) a₀) (f0 (subst* A p₁) a₁)}
         {r : HomEq Γ k₀ k₁ p₀ p₁}
         where

  IxHomEq-R : IxHom A p (f0 (subst* A p₀) a₀) (f0 (subst* A p₁) a₁)
            -> IxHomEq A r j₀ j₁
                       (R (∣ A ∣* _) (f0 (subst* A p₀) a₀))
                       (R (∣ A ∣* _) (f0 (subst* A p₁) a₁))
  IxHomEq-R m = {!m!}

module _ (A : Ty j Γ) {γ₀ γ₁ γ₀' γ₁' a₀ a₁}
         {p : Hom Γ γ₀ γ₁}
         -- {p₀ : Hom Γ γ₀' γ₀} {p₁ : Hom Γ γ₁' γ₁}
         -- {k₀ : Hom Γ γ₀' γ₁'} {k₁ : Hom Γ γ₀ γ₁}
         -- {j₀ : IxHom A k₀ a₀ a₁} {j₁ : IxHom A k₁ (f0 (subst* A p₀) a₀) (f0 (subst* A p₁) a₁)}
         -- {r : HomEq Γ k₀ k₁ p₀ p₁}
         where

  IxHomEq-R' : IxHom A p a₀ a₁
            -> IxHomEq A {!!} {!!} {!!}
                       {!R (∣ A ∣* _) ?!}
                       (R (∣ A ∣* _) {!!})
  IxHomEq-R' m = {!m!}

_‣_ : (Γ : Con i) -> Ty j Γ -> Con (i ⊔ j)
Γ ‣ A = record
  { ∣_∣ = Σ ∣ Γ ∣ λ γ → ∣ ∣ A ∣* γ ∣
  ; Hom = λ { (γ , a) (γ' , a') → Σ (Hom Γ γ γ') λ p → IxHom A p a a' }
  ; R = λ { (γ , a) → R Γ γ , IxR A a }
  ; S = λ { {γ , a} {γ' , a'} (p , q) → S Γ p , IxS A q }
  ; T = λ { (p , q) (p' , q') → T Γ p p' , IxT A q q' }
  ; id1 = sp (id1 Γ) (id1* A _)
  ; id2 = sp (id2 Γ) (id2* A _)
  ; assoc = λ { {p = _ , p} {_ , q} {_ , r} → sp (assoc Γ) (assoc* A p q r) }
  ; inv1 = λ { {p = p} → sp (inv1 Γ) (inv1* A (proj₂ p)) }
  ; inv2 = λ { {p = p} → sp (inv2 Γ) (inv2* A (proj₂ p)) }
  }

module _ {Γ : Con i} {A : Ty j Γ} {γ₀ γ₀' γ₁ γ₁' a₀ a₀' a₁ a₁'}
         {p₀ : Hom Γ γ₀ γ₀'} {p₁ : Hom Γ γ₁ γ₁'}
         {k₀ : Hom Γ γ₀ γ₁} {k₁ : Hom Γ γ₀' γ₁'}
         {q₀ : IxHom A p₀ a₀ a₀'} {q₁ : IxHom A p₁ a₁ a₁'}
         {f₀ : IxHom A k₀ a₀ a₁} {f₁ : IxHom A k₁ a₀' a₁'}
         where

  HomEq‣ : HomEq (Γ ‣ A) (k₀ , f₀) (k₁ , f₁) (p₀ , q₀) (p₁ , q₁)
         ≡ ΣP (HomEq Γ k₀ k₁ p₀ p₁) λ r → IxHomEq A r f₀ f₁ q₀ q₁
  HomEq‣ = refl (HomEq (Γ ‣ A) (k₀ , f₀) (k₁ , f₁) (p₀ , q₀) (p₁ , q₁))

module _ {Γ : Con i} (A : Ty j Γ) where

--   refl*1' : ∀{γ x y} {p : Hom (∣ A ∣* γ) x y}
--           -- -> HEq (λ w → Hom (∣ A ∣* γ) (proj₁ w) (proj₂ w))
--           --        (sp (trans {A = ∣ ∣ A ∣* _ ∣} (cong (λ z → f0 (subst* A z) x) (sym {A = Hom Γ _ _} ff)) (refl*0 A _)) {!!})
--           --        (f1 (subst* A q) p) p
--           -> HEq (λ w → Hom (∣ A ∣* γ) (proj₁ w) (proj₂ w))
--                  (sp (refl*0 A _) (fromEq (λ _ → ∣ ∣ A ∣* γ ∣) (refl*0 A _))) (f1 (subst* A (R Γ _)) p) p
-- -- {!f1 (subst* A q) p!} ≡ p
--           -- HomEq (∣ A ∣* γ) (f1 (subst* A q) p) p
--   refl*1' = {!!}
