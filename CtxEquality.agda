{-# OPTIONS --prop --rewriting --without-K --allow-unsolved-metas #-}

module CtxEquality where

open import Data.Product
open import Util
open import Equality
open import Groupoid
open import Substitution
open import Ty
open import Tm
open import Universes

_~ : (Γ : Con i) -> (γ₀ γ₁ : Δ ⟶ Γ) -> Tm Δ (Set-ty i)
_~ {Δ = Δ} Γ γ₀ γ₁ = record
  { tm0 = λ δ → Hom Γ (f0 γ₀ δ) (f0 γ₁ δ)
  ; tm1 = λ p → 
    record
    { iso1 = λ q → T Γ (S Γ (f1 γ₀ p)) (T Γ q (f1 γ₁ p))
    ; iso2 = λ q → T Γ (f1 γ₀ p) (T Γ q (S Γ (f1 γ₁ p)))
    ; prf1 = λ q →
        let open Eq-Reasoning (Hom Γ _ _)
            _∙_ = hom-tr Γ
            s = hom-sy Γ
        in begin
             _ ≡⟨ cong (T Γ (f1 γ₀ p)) (s (assoc Γ)
                ∙ cong (T Γ (S Γ (f1 γ₀ p))) (s (assoc Γ)
                ∙ (cong (T Γ q) (inv1 Γ) ∙ id1 Γ))) ⟩
             _ ≡⟨ assoc Γ ⟩
             _ ≡⟨ cong (λ z → T Γ z q) (inv1 Γ) ⟩
             _ ≡⟨ id2 Γ ⟩
             _ ∎
    ; prf2 = λ q →
        let open Eq-Reasoning (Hom Γ _ _)
            _∙_ = hom-tr Γ
            s = hom-sy Γ
        in begin
             _ ≡⟨ cong (T Γ (S Γ (f1 γ₀ p))) (s (assoc Γ)
                ∙ cong (T Γ (f1 γ₀ p)) (s (assoc Γ) ∙ (cong (T Γ q) (inv2 Γ)
                ∙ id1 Γ))) ⟩
             _ ≡⟨ assoc Γ ∙ (cong (λ z → T Γ z q) (inv2 Γ) ∙ id2 Γ) ⟩
             _ ∎
    }
  ; tm-refl = let open Eq-Reasoning (Hom Γ _ _) ; _∙_ = hom-tr Γ ; s = hom-sy Γ in
       sp' (λ p → ≡-to-HEq (begin
                _ ≡⟨ cong (λ z → T Γ (S Γ z) (T Γ _ _)) (f-R γ₀) ⟩
                _ ≡⟨ cong (λ z → T Γ (S Γ _) (T Γ _ z)) (f-R γ₁) ⟩
                _ ≡⟨ cong (T Γ (S Γ _)) (id1 Γ) ⟩
                _ ≡⟨ cong (λ z → T Γ z _) (S-id Γ) ⟩
                _ ≡⟨ id2 Γ ∙ p ⟩
                _ ∎))
           (λ p → ≡-to-HEq (begin
                _ ≡⟨ cong (λ z → T Γ _ (T Γ _ z)) (cong (S Γ) (f-R γ₁) ∙ S-id Γ) ⟩
                _ ≡⟨ cong (λ z → T Γ z (T Γ _ _)) (f-R γ₀) ∙ (id2 Γ ∙ (id1 Γ ∙ p)) ⟩
                _ ∎))

  ; tm-trans = {!!} -- Iso≡ (λ q → {!!}) {!!}
  }

R~ : ∀ (γ : Δ ⟶ Γ) -> Tm Δ (El-set ((Γ ~) γ γ))
R~ {Γ = Γ} γ = record
  { tm0 = λ _ → R Γ _
  ; tm1 = λ p →
      lift (trans {A = Hom Γ _ _} (cong (T Γ (S Γ (f1 γ p))) (id2 Γ)) (inv2 Γ))
  ; tm-refl = tt
  ; tm-trans = tt
  }

S~ : ∀ (γ₀ γ₁ : Δ ⟶ Γ) -> Tm Δ (El-set ((Γ ~) γ₀ γ₁)) -> Tm Δ (El-set ((Γ ~) γ₁ γ₀))
S~ {Γ = Γ} γ₀ γ₁ p = record
  { tm0 = λ δ → S Γ (tm0 p δ)
  ; tm1 = λ {δ1} {δ2} q →
        let lift aux = tm1 p q
            _∙_ = trans {A = Hom Γ _ _}
            sy = sym {A = Hom Γ _ _}
            aux'' = sy (S-reverse Γ ∙ (cong (T Γ (S Γ (T Γ _ _))) (SS-id Γ)
                  ∙ (cong (λ z -> T Γ z _) (S-reverse Γ) ∙ sy (assoc Γ))))
        in lift (aux'' ∙ cong (S Γ) aux)
  ; tm-refl = tt
  ; tm-trans = tt
  }

T~ : ∀ (γ₀ γ₁ γ₂ : Δ ⟶ Γ)
   -> Tm Δ (El-set ((Γ ~) γ₀ γ₁))
   -> Tm Δ (El-set ((Γ ~) γ₁ γ₂))
   -> Tm Δ (El-set ((Γ ~) γ₀ γ₂))
T~ {Γ = Γ} γ₀ γ₁ γ₂ p q = record
  { tm0 = λ δ → T Γ (tm0 p δ) (tm0 q δ)
  ; tm1 = λ r →
      let lift aux1 = tm1 p r
          lift aux2 = tm1 q r
          open Eq-Reasoning (Hom Γ _ _)
          goal = begin
            _ ≡⟨ cong (T Γ _) (sym {A = Hom Γ _ _} (assoc Γ)) ⟩
            _ ≡⟨ cong (T Γ _) (cong (T Γ _) (sym {A = Hom Γ _ _} (id2 Γ))) ⟩
            _ ≡⟨ cong (λ z → T Γ (S Γ _) (T Γ _ (T Γ z (T Γ _ _)))) (sym {A = Hom Γ _ _} (inv1 Γ)) ⟩
            _ ≡⟨ cong (T Γ _) (cong (T Γ _) (sym {A = Hom Γ _ _} (assoc Γ))) ⟩
            _ ≡⟨ cong (T Γ _) (assoc Γ) ⟩
            _ ≡⟨ assoc Γ ⟩
            _ ≡⟨ cong (λ z → T Γ z (T Γ _ (T Γ _ _))) aux1 ⟩
            _ ≡⟨ cong (T Γ _) aux2 ⟩
            _ ∎
      in lift goal
  ; tm-refl = tt
  ; tm-trans = tt
  }

module _ {Γ : Con i} {γ₀ γ₁ : Δ ⟶ Γ} {ρ : Ω ⟶ Δ} where

  Γ~[] : (((Γ ~) γ₀ γ₁) [ ρ ]') ≡ (Γ ~) (comp-fun ρ γ₀) (comp-fun ρ γ₁)
  Γ~[] = refl (((Γ ~) γ₀ γ₁) [ ρ ]')

module _ {ρ : Δ ⟶ Γ} {γ : Ω ⟶ Δ} where

  R~[] : ((R~ ρ) [ γ ]') ≡ R~ (comp-fun γ ρ)
  R~[] = refl (R~ ρ [ γ ]')

module _ {γ₀ γ₁ : Δ ⟶ Γ} {p : Tm Δ (El-set ((Γ ~) γ₀ γ₁))} {ρ : Ω ⟶ Δ} where

  S~[] : ((S~ γ₀ γ₁ p) [ ρ ]') ≡ S~ (comp-fun ρ γ₀) (comp-fun ρ γ₁) (p [ ρ ]')
  S~[] = refl ((S~ γ₀ γ₁ p) [ ρ ]')

module _ {γ₀ γ₁ γ₂ : Δ ⟶ Γ}
         {p : Tm Δ (El-set ((Γ ~) γ₀ γ₁))}
         {q : Tm Δ (El-set ((Γ ~) γ₁ γ₂))}
         {ρ : Ω ⟶ Δ} where

  T~[] : (T~ γ₀ γ₁ γ₂ p q [ ρ ]')
       ≡ T~ (comp-fun ρ γ₀) (comp-fun ρ γ₁) (comp-fun ρ γ₂) (p [ ρ ]') (q [ ρ ]')
  T~[] = refl (T~ γ₀ γ₁ γ₂ p q [ ρ ]')

module _ {Δ : Con k} (Γ : Con i) (ρ₀ ρ₁ : Ω ⟶ Γ) (γ₀ γ₁ : Δ ⟶ Ω)
         (p : Tm Δ (El-set ((Ω ~) γ₀ γ₁)))
         (r₀ : Tm Δ (El-set ((Γ ~) (comp-fun γ₀ ρ₀) (comp-fun γ₀ ρ₁))))
         (r₁ : Tm Δ (El-set ((Γ ~) (comp-fun γ₁ ρ₀) (comp-fun γ₁ ρ₁))))
         where

  _~~ : Tm Δ (El-set (Prop-set i))
  _~~ = record
    { tm0 = λ δ →
        HomEq Γ (f1 ρ₀ (tm0 p δ)) (f1 ρ₁ (tm0 p δ)) (tm0 r₀ δ) (tm0 r₁ δ)
    ; tm1 = λ {δ} {δ'} q →
        let qqq = reverse-HomEq Ω (unlift (tm1 p q))
            hhh = congHomEq ρ₀ (HomEq-S-reverse Ω qqq)
            eq = trans {A = Prop i} (cong (HomEq Γ _ _ _) (f-S ρ₀)) (cong (λ z → HomEq Γ _ _ z (S Γ _)) (f-S ρ₀))
        in lift (HomEq-≡ Γ (unlift (tm1 r₀ q)) (unlift (tm1 r₁ q)) (congHomEq ρ₁ qqq) (fst' eq hhh))
    ; tm-refl = tt
    ; tm-trans = tt
    }

module _ {∇ : Con i} {Δ : Con k} (Γ : Con i) (ρ₀ ρ₁ : Ω ⟶ Γ) (γ₀ γ₁ : Δ ⟶ Ω)
         (p : Tm Δ (El-set ((Ω ~) γ₀ γ₁)))
         (r₀ : Tm Δ (El-set ((Γ ~) (comp-fun γ₀ ρ₀) (comp-fun γ₀ ρ₁))))
         (r₁ : Tm Δ (El-set ((Γ ~) (comp-fun γ₁ ρ₀) (comp-fun γ₁ ρ₁))))
         (τ : ∇ ⟶ Δ)
         where

  ~~[] : (((Γ ~~) ρ₀ ρ₁ γ₀ γ₁ p r₀ r₁) [ τ ]')
       ≡ (Γ ~~) ρ₀ ρ₁ (comp-fun τ γ₀) (comp-fun τ γ₁) (p [ τ ]') (r₀ [ τ ]') (r₁ [ τ ]')
  ~~[] = refl (((Γ ~~) ρ₀ ρ₁ γ₀ γ₁ p r₀ r₁) [ τ ]')

module _ {Δ : Con k} (Γ : Con i) (ρ : Ω ⟶ Γ) (γ : Δ ⟶ Ω)
         (r : Tm Δ (El-set ((Γ ~) (comp-fun γ ρ) (comp-fun γ ρ))))
         where

  R~~ : Tm Δ (El-prop ((Γ ~~) ρ ρ γ γ (R~ γ) r r))
  R~~ = record
    { tm0 = λ δ →
        let aux = HomEq-R Γ (tm0 r δ)
            eq = trans {A = Prop i} (cong (λ z → HomEq Γ (f1 ρ (R Ω _)) z _ _) (f-R ρ))
                   (cong (λ z → HomEq Γ z (R Γ (f0 ρ _)) _ _) (f-R ρ))
        in lift (snd' eq aux)
    ; tm1 = λ _ → lift tt
    ; tm-refl = tt
    ; tm-trans = tt
    }

module _ {Δ : Con k} (Γ : Con i) (ρ₀ ρ₁ : Ω ⟶ Γ) (γ₀ γ₁ : Δ ⟶ Ω)
         (p : Tm Δ (El-set ((Ω ~) γ₀ γ₁)))
         (r₀ : Tm Δ (El-set ((Γ ~) (comp-fun γ₀ ρ₀) (comp-fun γ₀ ρ₁))))
         (r₁ : Tm Δ (El-set ((Γ ~) (comp-fun γ₁ ρ₀) (comp-fun γ₁ ρ₁))))
         (eq : Tm Δ (El-prop ((Γ ~~) ρ₀ ρ₁ γ₀ γ₁ p r₀ r₁)))
         where

  S~~ : Tm Δ (El-prop ((Γ ~~) ρ₀ ρ₁ γ₁ γ₀ (S~ γ₀ γ₁ p) r₁ r₀))
  S~~ = record
    { tm0 = λ δ →
        let aux = HomEq-S Γ (unlift (tm0 eq δ))
            eq : HomEq Γ (S Γ (f1 ρ₀ (tm0 p δ))) (S Γ (f1 ρ₁ (tm0 p δ))) _ _
               ≡ HomEq Γ (f1 ρ₀ (S Ω (tm0 p δ))) (f1 ρ₁ (S Ω (tm0 p δ))) _ _
            eq = trans {A = Prop i} (cong (λ z → HomEq Γ (S Γ _) z _ _) (sym {A = Hom Γ _ _} (f-S ρ₁)))
                       (cong (λ z → HomEq Γ z (f1 ρ₁ (S Ω _)) _ _) (sym {A = Hom Γ _ _} (f-S ρ₀)))
        in lift (fst' eq aux)
    ; tm1 = λ _ → lift tt
    ; tm-refl = tt
    ; tm-trans = tt
    }

module _ (Γ : Con i) {ρ₀ ρ₁ : Δ ⟶ Γ} (p : Tm Δ (El-set ((Γ ~) ρ₀ ρ₁))) where

  id1~~ : Tm Δ (El-prop ((Γ ~~) ρ₀ ρ₁ (id-fun Δ) (id-fun Δ) (R~ (id-fun Δ)) (T~ ρ₀ ρ₁ ρ₁ p (R~ ρ₁)) p))
  id1~~ = record
    { tm0 = λ δ →
        lift (snd' (HomEq-eq12 Γ (f-R ρ₀) (f-R ρ₁))
             (snd' (HomEq-eq34 Γ (id1 Γ) (refl (tm0 p δ)))
             (HomEq-R Γ (tm0 p δ))))
    ; tm1 = λ _ → lift tt
    ; tm-refl = tt
    ; tm-trans = tt
    }

  id2~~ : Tm Δ (El-prop ((Γ ~~) ρ₀ ρ₁ (id-fun Δ) (id-fun Δ) (R~ (id-fun Δ)) (T~ ρ₀ ρ₀ ρ₁ (R~ ρ₀) p) p))
  id2~~ = record
    { tm0 = λ δ → let tr = hom-tr Γ in
        lift (snd' (HomEq-eq12 Γ (f-R ρ₀) (f-R ρ₁))
             (snd' (HomEq-eq34 Γ (id2 Γ) (refl (tm0 p _)))
             (tr (cong (T Γ (S Γ _)) (id1 Γ))
             (tr (cong (λ z → T Γ z _) (S-id Γ)) (id2 Γ)))))
    ; tm1 = λ _ → lift tt
    ; tm-refl = tt
    ; tm-trans = tt
    }
