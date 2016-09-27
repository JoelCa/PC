module Functors.Cat where

open import Library
open import Categories
open import Functors
open import Naturals

idlNat : ∀{a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}{F G : Fun C D}
         {α : NatT F G} → compVNat idNat α ≅ α
idlNat {D = D} = NatTEq (iext λ _ → Cat.idl D)

idrNat : ∀{a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}{F G : Fun C D}
         {α : NatT F G} → compVNat α idNat ≅ α
idrNat {D = D} = NatTEq (iext λ _ → Cat.idr D)
 
assNat : ∀{a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}{E F G H : Fun C D}
         {α : NatT G H}{β : NatT F G}{η : NatT E F} → 
         compVNat (compVNat α β) η ≅ compVNat α (compVNat β η)
assNat {D = D} = NatTEq (iext λ _ → Cat.ass D)

FunctorCat : ∀{a b c d} → Cat {a}{b} → Cat {c}{d} → Cat
FunctorCat C D = record{
  Obj  = Fun C D;
  Hom  = NatT;
  iden = idNat;
  _∙_  = compVNat;
  idl  = idlNat;
  idr  = idrNat;
  ass  = λ{_}{_}{_}{_}{α}{β}{η} → assNat {α = α}{β}{η}}


