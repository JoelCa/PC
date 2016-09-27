module Categories.Initial where

open import Library
open import Categories
open import Categories.Sets
open Cat

{- Objeto inicial en una categoría -}

record Init {a b} (C : Cat {a}{b})(I : Obj C) : Set (a ⊔ b) where
  constructor init
  field i : ∀{X} → Hom C I X
        law : ∀{X}{f : Hom C I X} → i {X} ≅ f 

ZeroSet : Init Sets ⊥
ZeroSet = record {i = λ(); law = ext λ()}

open Init

{- el morfismo universal del objeto inicial a sí mismo es la identidad -}

init-iden : ∀{a b} {C : Cat {a}{b}}(I : Obj C){init : Init C I}
          → i init {I} ≅ iden C {I}
init-iden I {init i law} = law
