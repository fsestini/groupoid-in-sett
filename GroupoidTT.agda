{-# OPTIONS --prop --without-K #-}

module GroupoidTT where

open import Agda.Primitive
open import Equality

private
  variable
    i j k l : Level

record CwF-structure : Setω where
  field
    Con : (i : Level) -> Set i
    Ty  : (j : Level) -> Con i -> Set j
    Tm  : (Γ : Con i) (A : Ty j Γ) -> Set (i ⊔ j)
    Sub : Con i -> Con j -> Set (i ⊔ j)

    _[_] : {Γ : Con i} {Δ : Con k} -> Ty j Γ -> Sub Δ Γ -> Ty j Δ
    _[_]' : {Γ : Con i} {Δ : Con k} {A : Ty j Γ} -> Tm Γ A -> (σ : Sub Δ Γ)
          -> Tm Δ (A [ σ ])

    _∘_ : {Γ : Con i} {Δ : Con j} {∇ : Con k}
        → Sub Δ ∇ → Sub Γ Δ → Sub Γ ∇

    -- and so on...

record Universes-structure (M : CwF-structure) : Setω where
  open CwF-structure M
  field
    Set-ty : {Γ : Con i} (j : Level) -> Ty j Γ
    El-set : {Γ : Con i} -> Tm Γ (Set-ty j) -> Ty (lsuc j) Γ

    Prop-set : {Γ : Con i} (j : Level) -> Tm Γ (Set-ty (lsuc j))
    El-prop  : {Γ : Con i} -> Tm Γ (El-set (Prop-set j)) -> Tm Γ (Set-ty (lsuc j))

    Set[] : {Γ : Con i} {Δ : Con k} (σ : Sub Δ Γ)
          -> ((Set-ty j) [ σ ]) ≡ Set-ty j

record CtxEquality-structure
       (M : CwF-structure)
       (U : Universes-structure M) : Setω where
  open CwF-structure M
  open Universes-structure U

  field
    _~  : (Γ : Con i) {Δ : Con k} -> Sub Δ Γ -> Sub Δ Γ -> Tm Δ (Set-ty i)

    R~ : {Γ : Con i} {Δ : Con k} (γ : Sub Δ Γ) -> Tm Δ (El-set ((Γ ~) γ γ))
    S~ : {Γ : Con i} {Δ : Con k} (γ₀ γ₁ : Sub Δ Γ)
       -> Tm Δ (El-set ((Γ ~) γ₀ γ₁)) -> Tm Δ (El-set ((Γ ~) γ₁ γ₀))
    T~ : {Γ : Con i} {Δ : Con k} (γ₀ γ₁ γ₂ : Sub Δ Γ)
       -> Tm Δ (El-set ((Γ ~) γ₀ γ₁))
       -> Tm Δ (El-set ((Γ ~) γ₁ γ₂))
       -> Tm Δ (El-set ((Γ ~) γ₀ γ₂))

    Γ~[] : {Γ : Con i} {Δ : Con k} {Ω : Con j} {γ₀ γ₁ : Sub Δ Γ} {ρ : Sub Ω Δ}
         → coe (Tm _) (Set[] _) (((Γ ~) γ₀ γ₁) [ ρ ]')
         ≡ (Γ ~) (γ₀ ∘ ρ) (γ₁ ∘ ρ)

    -- and so on...

    _~~ : (Γ : Con i) {Δ : Con k} {Ω : Con j}
          (ρ₀ ρ₁ : Sub Ω Γ) (γ₀ γ₁ : Sub Δ Ω)
          (p : Tm Δ (El-set ((Ω ~) γ₀ γ₁)))
          (r₀ : Tm Δ (El-set ((Γ ~) (ρ₀ ∘ γ₀) (ρ₁ ∘ γ₀))))
          (r₁ : Tm Δ (El-set ((Γ ~) (ρ₀ ∘ γ₁) (ρ₁ ∘ γ₁))))
        → Tm Δ (El-set (Prop-set i))
  
    -- and so on...
