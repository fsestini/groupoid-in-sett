{-# OPTIONS --prop --rewriting --without-K --allow-unsolved-metas #-}

module Groupoid where

open import Agda.Builtin.Equality renaming (_≡_ to _⇒_ ; refl to reduce)
open import Agda.Builtin.Equality.Rewrite

open import Data.Product
open import Util
open import SetoidEquality hiding (R ; S ; T)

record Groupoid (i : Level) : Set (lsuc i) where
  no-eta-equality
  field
    ∣_∣ : Set i
    Hom : ∣_∣ -> ∣_∣ -> Set i

    R : ∀ x -> Hom x x
    S : ∀{x y} -> Hom x y -> Hom y x
    T : ∀{x y z} -> Hom x y -> Hom y z -> Hom x z

    id1 : ∀{x y} {p : Hom x y} -> T p (R _) ≡ p
    id2 : ∀{x y} {p : Hom x y} -> T (R _) p ≡ p
    assoc : ∀{x y z w} {p : Hom x y} {q : Hom y z} {r : Hom z w}
          -> T p (T q r) ≡ T (T p q) r
    inv1 : ∀{x y} {p : Hom x y} -> T p (S p) ≡ R _
    inv2 : ∀{x y} {p : Hom x y} -> T (S p) p ≡ R _
open Groupoid public

Con = Groupoid

postulate
  Groupoid≡ : {i : Level} {G H : Groupoid i} {Γ : Set k} {x y : Γ} {p : Eq Γ x y}
      -> HEq {Γ = Γ} (λ _ -> Groupoid i) p G H
       ⇒ ΣP (∣ G ∣ ≡ ∣ H ∣) λ eq1
       → ΣP (Het (λ X → X -> X -> Set i) eq1 (Hom G) (Hom H)) λ eq2
       → Het {A = Σ (Set i) (λ X → X → X → Set i)}
              (λ { (X , Rel) → ∀ {x1} {x2} {x3} → Rel x1 x2 → Rel x2 x3 → Rel x1 x3 })
              {∣ G ∣ , Hom G} {∣ H ∣ , Hom H}
              (sp eq1 eq2) (T G) (T H)
{-# REWRITE Groupoid≡ #-}

hom-sy : (G : Groupoid i) {a b : _} {p q : Hom G a b} → p ≡ q -> q ≡ p
hom-sy G {a} {b} = sym (Hom G a b)

hom-tr : (G : Groupoid i) {a b : _} {p q r : Hom G a b} → p ≡ q → q ≡ r → p ≡ r
hom-tr G {a} {b} = trans (Hom G a b)

module _ (Γ : Con i) where

  HomEq : ∀{a b c d} -> Hom Γ a c -> Hom Γ b d -> Hom Γ a b -> Hom Γ c d -> Prop _
  HomEq x y p q = T Γ (S Γ x) (T Γ p y) ≡ q

module _ (Γ : Con i) {a b} (p : Hom Γ a b) where

  HomEq-R : HomEq Γ (R Γ a) (R Γ b) p p
  HomEq-R = {!!}

module _ (Γ : Con i) {a b c d}
         {k1 : Hom Γ a c} {k2 : Hom Γ b d} {p : Hom Γ a b} {q : Hom Γ c d}
         (eq : HomEq Γ k1 k2 p q) where

  HomEq-S : HomEq Γ (S Γ k1) (S Γ k2) q p
  HomEq-S = {!!}

module _ (Γ : Con i) {a b c d}
         {k1 k1' : Hom Γ a c} {k2 k2' : Hom Γ b d} {p : Hom Γ a b} {q : Hom Γ c d}
         (eq1 : k1 ≡ k1') (eq2 : k2 ≡ k2')
         where

  HomEq-eq12 : HomEq Γ k1 k2 p q ≡ HomEq Γ k1' k2' p q
  HomEq-eq12 = trans (Prop i) (cong (λ z → HomEq Γ z k2 p q) eq1)
                              (cong (λ z → HomEq Γ _ z p q) eq2)

module _ (Γ : Con i) {a b c d}
         {k1 : Hom Γ a c} {k2 : Hom Γ b d} {p p' : Hom Γ a b} {q q' : Hom Γ c d}
         (eq1 : p ≡ p') (eq2 : q ≡ q')
         where

  HomEq-eq34 : HomEq Γ k1 k2 p q ≡ HomEq Γ k1 k2 p' q'
  HomEq-eq34 = trans (Prop i) (cong (λ z → HomEq Γ _ _ z q) eq1)
                              (cong (λ z → HomEq Γ _ _ _ z) eq2)

module _ (Γ : Con i) {a b c d} {x : Hom Γ a c} {y : Hom Γ b d} {p : Hom Γ a b} {q : Hom Γ c d}
         {a' b' c' d'}
           {x' : Hom Γ a' c'} {y' : Hom Γ b' d'} {p' : Hom Γ a' b'} {q' : Hom Γ c' d'}

       {x1 : Hom Γ a a'} {y1 : Hom Γ b b'}
       (eq1 : HomEq Γ x1 y1 p p')
       {x2 : Hom Γ c c'} {y2 : Hom Γ d d'}
       (eq2 : HomEq Γ x2 y2 q q')
       (eq-bottom : HomEq Γ y y' y1 y2)
       (eq-top : HomEq Γ x' x (S Γ x1) (S Γ x2))
       where

  HomEq-≡ : HomEq Γ x y p q ≡ HomEq Γ x' y' p' q'
  HomEq-≡ = sp' equiv1 equiv2
    where
      open Eq-Reasoning (Hom Γ _ _)
      _∙'_ = hom-tr Γ
      s = hom-sy Γ
      equiv1 : T Γ (S Γ x) (T Γ p y) ≡ q
             → T Γ (S Γ x') (T Γ p' y') ≡ q'
      equiv1 eq =
        begin
          _ ≡⟨ cong (T Γ (S Γ x')) (cong (λ z → T Γ z y') (s eq1)
              ∙' s (cong (T Γ (S Γ x1)) (assoc Γ) ∙' assoc Γ)) ∙' assoc Γ ⟩
          _ ≡⟨ cong (λ z → T Γ z (T Γ p (T Γ y1 y'))) ((cong (T Γ (S Γ x'))
                (s (cong (T Γ (S Γ x1)) (inv1 Γ) ∙' id1 Γ) ∙' assoc Γ) ∙' assoc Γ)
                ∙' cong (λ z → T Γ z (S Γ x)) eq-top) ⟩
          _ ≡⟨ s (assoc Γ) ⟩
          _ ≡⟨ cong (T Γ (S Γ x2)) (cong (T Γ (S Γ x)) (cong (T Γ p)
                (s (assoc Γ ∙' (cong (λ z → T Γ z (T Γ _ _)) (inv1 Γ) ∙' id2 Γ)))
                ∙' assoc Γ) ∙' assoc Γ) ⟩
          _ ≡⟨ cong (λ z → T Γ _ (T Γ (T Γ _ (T Γ p y)) z)) eq-bottom ⟩
          _ ≡⟨ cong (λ z → T Γ _ (T Γ z _)) eq ⟩
          _ ≡⟨ eq2 ⟩
          _ ∎
      equiv2 : T Γ (S Γ x') (T Γ p' y') ≡ q'
             → T Γ (S Γ x) (T Γ p y) ≡ q
      equiv2 eq = {!!}

module _ (G : Groupoid i) {x y : ∣ G ∣} {p : Hom G x y} where

  inv-unique : {q : Hom G y x} -> T G p q ≡ R G _ -> S G p ≡ q
  inv-unique {q = q} eq = sy (sy (id2 G) ∙ aux'' ∙ aux' ∙ (aux ∙ id1 G))
    where open Eq-Reasoning (Hom G _ _)
          aux = cong (T G (S G p)) eq
          aux' = sy (assoc G {p = S G p} {p} {q})
          aux'' = cong (λ z → T G z q) (sym (Hom G _ _) (inv2 G))

module _ (G : Groupoid i) {x y : ∣ G ∣} {p : Hom G x y} where

  SS-id : S G (S G p) ≡ p
  SS-id = inv-unique G (inv2 G)

module _ (G : Groupoid i) {x : ∣ G ∣} where

  S-id : S G (R G x) ≡ R G x
  S-id = inv-unique G (id1 G)

module _ (G : Groupoid i) {x y z : ∣ G ∣} {p : Hom G x y} {q : Hom G y z} where

  S-reverse : S G (T G p q) ≡ T G (S G q) (S G p)
  S-reverse = inv-unique G {p = T G p q} {T G (S G q) (S G p)} goal
    where
      open Eq-Reasoning (Hom G _ _)
      _∙'_ = hom-tr G
      goal = begin
        _ ≡⟨ sym (Hom G _ _) (assoc G) ⟩
        _ ≡⟨ cong (T G p) ((assoc G ∙' cong (λ z → T G z (S G _)) (inv1 G)) ∙' id2 G) ⟩
        _ ≡⟨ inv1 G ⟩
        _ ∎

variable Γ Δ Ω ∇ : Con i

record _⟶_ (G : Groupoid i) (H : Groupoid j) : Set (i ⊔ j) where
  no-eta-equality
  field
    f0 : ∣ G ∣ -> ∣ H ∣
    f1 : ∀{x y} -> Hom G x y -> Hom H (f0 x) (f0 y)

    f-R : ∀{x} -> f1 (R G x) ≡ R H _
    f-T : ∀{x y z} (p : Hom G x y) (q : Hom G y z)
        -> f1 (T G p q) ≡ T H (f1 p) (f1 q)
open _⟶_ public

id-fun : (Γ : Con i) -> Γ ⟶ Γ
id-fun Γ =
  record { f0 = λ z → z ; f1 = λ z → z
         ; f-R = refl (Hom Γ _ _) ; f-T = λ p q → refl (Hom Γ _ _) }

postulate
  ⟶≡ : {H1 : Groupoid i} {H2 : Groupoid j} {F G : H1 ⟶ H2} {Γ : Set k} {x y : Γ} {p : Eq Γ x y}
      -> HEq {Γ = Γ} (λ _ -> H1 ⟶ H2) p F G
        ⇒ ΣP (f0 F ≡ f0 G) λ eq1
        → Het {A = ∣ H1 ∣ -> ∣ H2 ∣}
              (λ f → ∀{x y} -> Hom H1 x y -> Hom H2 (f x) (f y)) eq1
              (f1 F) (f1 G)
{-# REWRITE ⟶≡ #-}

module _ {G : Groupoid i} {H : Groupoid j} {K : Groupoid k} where

  comp-fun : G ⟶ H -> H ⟶ K -> G ⟶ K
  comp-fun h1 h2 = record
    { f0 = λ x → f0 h2 (f0 h1 x)
    ; f1 = λ x → f1 h2 (f1 h1 x)
    ; f-R = λ {x} -> trans (Hom K _ _) (cong (f1 h2) (f-R h1 {x})) (f-R h2)
    ; f-T = λ p q → trans (Hom K _ _) (cong (f1 h2) (f-T h1 p q)) (f-T h2 _ _)
    }

module _ (f : Γ ⟶ Δ) {a b} {p : Hom Γ a b} where

  f-S : f1 f (S Γ p) ≡ S Δ (f1 f p)
  f-S = s (inv-unique Δ (t (s (f-T f p (S Γ p))) (t (cong (f1 f) (inv1 Γ)) (f-R f))))
    where s = hom-sy Δ ; t = hom-tr Δ

module _ {Γ : Con i} {a b c d}{x : Hom Γ a c} {y : Hom Γ b d} {p : Hom Γ a b} {q : Hom Γ c d}
         (f : Γ ⟶ Δ)
         (eq : HomEq Γ x y p q) where

  congHomEq : HomEq Δ (f1 f x) (f1 f y) (f1 f p) (f1 f q)
  congHomEq = begin
    _ ≡⟨ cong (λ z → T Δ z (T Δ (f1 f p) (f1 f y))) (s' (f-S f)) ⟩
    _ ≡⟨ cong (T Δ (f1 f (S Γ x))) (s' (f-T f p y)) ⟩
    _ ≡⟨ sy (f-T f _ _) ⟩
    _ ≡⟨ cong (f1 f) eq ⟩
    _ ∎
    where open Eq-Reasoning (Hom Δ _ _) ; s = hom-sy Γ ; s' = hom-sy Δ

module _ (Γ : Con i) {a b c d} {x : Hom Γ a c} {y : Hom Γ b d}
         {p : Hom Γ a b} {q : Hom Γ c d} where

  reverse-HomEq : HomEq Γ x y p q -> HomEq Γ p q x y
  reverse-HomEq eq = {!!}   -- easy, just groupoid laws
                -- assoc Γ
                --    ∙ sym (cong (λ z -> T Γ (T Γ (S Γ p) x) z) eq)
                --    ∙ sym (assoc Γ)
                --    ∙ cong (T Γ (S Γ p)) (assoc Γ ∙ cong (λ z -> T Γ z _) (inv1 Γ))
                --    ∙ {!!}

  HomEq-S-reverse : HomEq Γ x y p q -> HomEq Γ y x (S Γ p) (S Γ q)
  HomEq-S-reverse = {!!} -- easy, just groupoid laws
