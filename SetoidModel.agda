{-# OPTIONS --prop --without-K #-}

module SetoidModel where

open import Util

record Con (i : Level) : Set (lsuc i) where
  field
    ∣_∣ : Set i
    Rel : ∣_∣ → ∣_∣ → Prop i
    R : ∀ γ → Rel γ γ
    S : ∀{γ γ'} → Rel γ γ' → Rel γ' γ
    T : ∀{γ γ' γ''} → Rel γ γ' → Rel γ' γ'' → Rel γ γ''
  infix 4 ∣_∣
open Con public

variable
  Γ Δ Ω ∇ : Con i

record Tms (Γ : Con i) (Δ : Con j) : Set (i ⊔ j) where
  field
    f0 : ∣ Γ ∣ → ∣ Δ ∣
    f1   : {γ γ' : ∣ Γ ∣} → Rel Γ γ γ' → Rel Δ (f0 γ) (f0 γ')
open Tms public

record Ty (j : Level) (Γ : Con i) : Set (lsuc j ⊔ i) where
  field
    ∣_∣*   : ∣ Γ ∣ → Set j
    Rel*   : ∀{γ γ'}(p : Rel Γ γ γ') → ∣_∣* γ → ∣_∣* γ' → Prop j
    R*     : ∀{γ} α → Rel* (R Γ γ) α α
    S*     : ∀{γ γ'}{p : Rel Γ γ γ'}{α : ∣_∣* γ}{α' : ∣_∣* γ'}
            → Rel* p α α' → Rel* (S Γ p) α' α
    T*     : ∀{γ γ' γ''}{p : Rel Γ γ γ'}{q : Rel Γ γ' γ''}
              {α : ∣_∣* γ}{α' : ∣_∣* γ'}{α'' : ∣_∣* γ''}
            → Rel* p α α' → Rel* q α' α'' → Rel* (T Γ p q) α α''
    coe    : {γ γ' : ∣ Γ ∣} → Rel Γ γ γ' → ∣_∣* γ → ∣_∣* γ'
    coh    : {γ γ' : ∣ Γ ∣}(p : Rel Γ γ γ')(α : ∣_∣* γ) → Rel* p α (coe p α)
  infix 4 ∣_∣*
open Ty public

record Tm (Γ : Con i) (A : Ty j Γ) : Set (i ⊔ j) where
  field
    ∣_∣t : (γ : ∣ Γ ∣) → ∣ A ∣* γ
    ~t   : {γ γ' : ∣ Γ ∣}(p : Rel Γ γ γ') → Rel* A p (∣_∣t γ) (∣_∣t γ')
  infix 4 ∣_∣t
open Tm public

• : Con lzero
• = record
  { ∣_∣   = Top
  ; Rel  = λ _ _ → ⊤
  }

open import Data.Product

_‣_ : (Γ : Con i) (A : Ty j Γ) -> Con _
Γ ‣ A = record
  { ∣_∣ = Σ ∣ Γ ∣ ∣ A ∣*
  ; Rel = λ { (γ , a) (γ' , a') → ΣP (Rel Γ γ γ') λ p → Rel* A p a a' }
  ; R = λ γ → sp (R Γ _) (R* A _)
  ; S = λ { (sp p q) → sp (S Γ p) (S* A q) }
  ; T = λ { (sp p q) (sp p' q') → sp (T Γ p p') (T* A q q') }
  }

_[_] : Ty j Δ -> Tms Γ Δ -> Ty j Γ
A [ σ ] = record
  { ∣_∣* = λ x → ∣ A ∣* (f0 σ x)
  ; Rel* = λ p → Rel* A (f1 σ p)
  ; R* = R* A
  ; S* = S* A
  ; T* = T* A
  ; coe = λ p a → coe A (f1 σ p) a
  ; coh = λ p a → coh A (f1 σ p) a
  }

id : (Γ : Con i) → Tms Γ Γ
id Γ = record { f0 = λ x → x ; f1 = λ x → x }

_∘_ : Tms Ω Δ → Tms Γ Ω → Tms Γ Δ
σ ∘ τ = record { f0 = λ x → f0 σ (f0 τ x) ; f1 = λ x → f1 σ (f1 τ x) }

ε : Tms Γ •
ε = record { f0 = λ _ → top ; f1 = λ _ → tt }

ext : (A : Ty j Δ) → (σ : Tms Γ Δ) -> Tm Γ (A [ σ ]) -> Tms Γ (Δ ‣ A)
ext A σ t = record
  { f0 = λ γ → f0 σ γ , ∣ t ∣t γ
  ; f1 = λ p → sp (f1 σ p) (~t t p)
  }

π₁ : (A : Ty j Δ) -> Tms Γ (Δ ‣ A) -> Tms Γ Δ
π₁ A σ = record { f0 = λ x → proj₁ (f0 σ x) ; f1 = λ x → fst (f1 σ x) }

_[_]' : {A : Ty j Γ} -> Tm Γ A → (σ : Tms Δ Γ) → Tm Δ (A [ σ ])
t [ σ ]' = record
  { ∣_∣t = λ δ → ∣ t ∣t (f0 σ δ)
  ; ~t = λ p → ~t t (f1 σ p)
  }

open import Relation.Binary.PropositionalEquality hiding ([_])

wk : (A : Ty j Γ) -> Tms (Γ ‣ A) Γ
wk {Γ = Γ} A = π₁ A (id (Γ ‣ A))

--------------------------------------------------

Prop-ty : (j : Level) -> Ty (lsuc j) Γ
Prop-ty j = record
  { ∣_∣* = λ γ → Prop j
  ; Rel* = λ p P Q → ΣP' (P -> Q) (λ _ → Q -> P)
  ; R* = λ α → sp' (λ x → x) (λ x → x)
  ; S* = λ x → sp' (snd' x) (fst' x)
  ; T* = λ p q → sp' (λ x → fst' q (fst' p x)) (λ x → snd' p (snd' q x))
  ; coe = {!!}
  ; coh = {!!}
  }

El : Tm Γ (Prop-ty j) -> Ty j Γ
El P = record
  { ∣_∣* = λ γ → Lift (∣ P ∣t γ)
  ; Rel* = λ _ _ _ → ⊤
  ; coe = λ { p (lift x) → lift (fst' (~t P p) x) }
  }

module _ (Γ : Con i) {Δ : Con j} where

  _~ : Tms Δ Γ -> Tms Δ Γ -> Tm Δ (Prop-ty _)
  _~ ρ₀ ρ₁ = record
    { ∣_∣t = λ γ → Rel Γ (f0 ρ₀ γ) (f0 ρ₁ γ)
    ; ~t = λ p → sp' (λ q → T Γ (S Γ (f1 ρ₀ p)) (T Γ q (f1 ρ₁ p)))
                     (λ q → T Γ (f1 ρ₀ p) (T Γ q (S Γ (f1 ρ₁ p))))
    }

  R~ : (ρ : Tms Δ Γ) -> Tm Δ (El (_~ ρ ρ))
  R~ ρ = record { ∣_∣t = λ δ → lift (R Γ _) }

module _ (δ : Tms Γ Δ) (ρ₀ ρ₁ : Tms Ω Γ) where

  _~s : Tm Ω (El ((Γ ~) ρ₀ ρ₁)) -> Tm Ω (El ((Δ ~) (δ ∘ ρ₀) (δ ∘ ρ₁)))
  _~s p = record { ∣_∣t = λ ω → lift (f1 δ (unlift (∣ p ∣t ω))) }

module _ (A : Ty j Γ) {Δ : Con i} where

  module _ (ρ₀ ρ₁ : Tms Δ Γ) (p : Tm Δ (El ((Γ ~) ρ₀ ρ₁))) where
    
    _~* : Tm Δ (A [ ρ₀ ]) -> Tm Δ (A [ ρ₁ ]) -> Tm Δ (Prop-ty _)
    _~* a₀ a₁ = record
      { ∣_∣t = λ δ → Rel* A (unlift (∣ p ∣t δ)) (∣ a₀ ∣t δ) (∣ a₁ ∣t δ)
      ; ~t = λ q → sp' (λ r → T* A (S* A (~t a₀ q)) (T* A r (~t a₁ q)))
                       (λ r → T* A (~t a₀ q) (T* A r (S* A (~t a₁ q))))
      }

    coe~ : Tm Δ (A [ ρ₀ ]) -> Tm Δ (A [ ρ₁ ])
    coe~ a = record
      { ∣_∣t = λ δ → coe A (unlift (∣ p ∣t δ)) (∣ a ∣t δ)
      ; ~t = λ q → T* A (S* A (coh A (unlift (∣ p ∣t _)) _))
                        (T* A (~t a q) (coh A (unlift (∣ p ∣t _)) _))
      }

  R~* : {ρ : Tms Δ Γ} (a : Tm Δ (A [ ρ ])) -> Tm Δ (El (_~* ρ ρ (R~ Γ ρ) a a))
  R~* a = record { ∣_∣t = λ γ → lift (R* A _) }


Id : (A : Ty j Γ) → Tm Γ A → Tm Γ A → Tm Γ (Prop-ty j)
Id {Γ = Γ} A a a' = (A ~*) (id Γ) (id Γ) (R~ Γ (id Γ)) a a'

module _ (A : Ty j Γ) (ρ₀ ρ₁ : Tms Δ Γ)
         (a₀ : Tm Δ (A [ ρ₀ ])) (a₁ : Tm Δ (A [ ρ₁ ])) where

  ext~ : (p : Tm Δ (El ((Γ ~) ρ₀ ρ₁)))
       → Tm Δ (El ((A ~*) ρ₀ ρ₁ p a₀ a₁))
       → Tm Δ (El (((Γ ‣ A) ~) (ext A ρ₀ a₀) (ext A ρ₁ a₁)))
  ext~ p~ a~ = record
    { ∣_∣t = λ δ → lift (sp (unlift (∣ p~ ∣t δ)) (unlift (∣ a~ ∣t δ))) }

module _ (A : Ty j Γ) (σ : Tms Δ Γ)
         (ρ₀ ρ₁ : Tms Ω Δ) (p : Tm Ω (El ((Δ ~) ρ₀ ρ₁)))
         (a : Tm Ω ((A [ σ ]) [ ρ₀ ])) where

  coe[] : coe~ (A [ σ ]) ρ₀ ρ₁ p a ≡ coe~ A (σ ∘ ρ₀) (σ ∘ ρ₁) ((σ ~s) ρ₀ ρ₁ p) a
  coe[] = refl

postulate
  coe~R : (A : Ty j Γ) (ρ : Tms Δ Γ) (a : Tm Δ (A [ ρ ]))
        → coe~ A ρ ρ (R~ Γ ρ) a ≡ a

module _ {A : Ty j Γ} (P : Ty k (Γ ‣ A))
         (a a' : Tm Γ A) where

  transp~ : Tm Γ (El (Id A a a'))
          -> Tm Γ (P [ ext A (id Γ) a ]) -> Tm Γ (P [ ext A (id Γ) a' ])
  transp~ p t =
    coe~ P (ext A (id Γ) a) (ext A (id Γ) a')
           (ext~ A (id Γ) (id Γ) a a' (R~ Γ (id Γ)) p) t

module _ {A : Ty j Γ} {σ : Tms Δ Γ} {t : Tm Δ (A [ σ ])} where

  wkex : wk A ∘ ext A σ t ≡ σ
  wkex = refl

module _ {A : Ty j Γ} {P : Ty k Γ}
         {a a' : Tm Γ A} {p : Tm Γ (El (Id A a a'))}
         {x : Tm Γ P} where

  open ≡-Reasoning

  ex = ext A (id Γ)

  transp-const : transp~ {A = A} (P [ wk A ]) a a' p x
  -- coe~ (P [ wk A ]) (ext A (id Γ) a) (ext A (id Γ) a') (ext~ A (id Γ) (id Γ) a a' (R~ Γ (id Γ)) p) x
  --               coe~ P (wk A ∘ ex a) (wk A ∘ ex a') ((wk A ~s) (ex a) (ex a') (ext~ A (id Γ) (id Γ) a a' (R~ Γ (id Γ)) p)) x
  -- transp~ {A = A} (P [ wk A ]) a a' p x
               ≡ x
  transp-const = begin
    {!!}
      ≡⟨ refl ⟩
    coe~ P (wk A ∘ ex a) (wk A ∘ ex a') ((wk A ~s) (ex a) (ex a') (ext~ A (id Γ) (id Γ) a a' (R~ Γ (id Γ)) p)) x
      ≡⟨ {!!} ⟩
    coe~ P (id Γ) (id Γ) (R~ Γ (id Γ)) x
      ≡⟨ coe~R P (id Γ) x ⟩
    {!!}
      ∎
