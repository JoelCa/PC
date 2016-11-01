
open import Categories
open import Categories.Products
open import Categories.Coproducts
open import Categories.Initial

module Categories.Distributive {a}{b}{C : Cat {a}{b}}
                               (hasProducts : Products C)
                               (hasCoproducts : Coproducts C)
                               (I : Cat.Obj C)
                               (hasInitial : Initial C I)
       where

open import Library hiding (_×_ ; _+_)
open import Categories.Iso public

open Cat C

open import Categories.Coproducts.Properties hasCoproducts
open Coproducts hasCoproducts

open Products hasProducts
open import Categories.Products.Properties hasProducts

open Initial hasInitial

--------------------------------------------------

undistr : ∀{X Y Z} → Hom (X × Y + X × Z) (X × (Y + Z))
undistr = [ pair iden inl , pair iden inr ]

unnull : ∀{X} → Hom I (X × I)
unnull = i

record Distributive : Set (a ⊔ b) where
  field
    distribute : ∀{X Y Z} → Iso C (undistr {X} {Y} {Z}) 
    nullify    : ∀{X} → Iso C (unnull {X})

  distr : ∀{X Y Z} → Hom (X × (Y + Z)) (X × Y + X × Z)
  distr {X}{Y}{Z} = Iso.inv (distribute {X} {Y} {Z})

