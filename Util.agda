{-# OPTIONS --prop --without-K #-}

module Util where

open import Agda.Primitive public

variable
  i j k l : Level

record ΣP {i j} (P : Prop i) (Q : P -> Prop j) : Prop (i ⊔ j) where
  constructor sp
  field
    fst : P
    snd : Q fst
open ΣP public

record Lift {i : Level} (P : Prop i) : Set i where
  constructor lift
  field
    unlift : P
open Lift public

-- record ΣSP {i j} (P : Set i) (Q : P -> Prop j) : Set (i ⊔ j) where
--   constructor sp
--   field
--     fst : P
--     snd : Q fst
-- open ΣP

record ⊤ {i : Level} : Prop i where
  constructor tt

record Top {i : Level} : Set i where
  constructor top

record ΣP' {i j} (P : Prop i) (Q : P -> Prop j) : Prop (lsuc (i ⊔ j)) where
  constructor sp'
  field
    fst' : P
    snd' : Q fst'
open ΣP' public
