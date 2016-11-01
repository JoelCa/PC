open import Categories
open import Categories.Products
open import Categories.Coproducts
open import Categories.Terminal
open import Categories.Initial

module Categories.CCC-CoproductsIsDist {a}{b}{C : Cat {a}{b}}
                                       {T : Cat.Obj C}
                                       {I : Cat.Obj C}
                                       (hasProducts : Products C)
                                       (hasCoproducts : Coproducts C)           
                                       (hasTerminal : Terminal C T)
                                       (hasInitial : Initial C I)
                                       where

open import Library hiding (_×_ ; _+_)
open import Categories.CartesianClosed

open Categories.CartesianClosed hasProducts T hasTerminal

open import Categories.Distributive --hiding (Distributive) 
--open Categories.Distributive hasProducts hasCoproducts I hasInitial

open Cat C
open Products hasProducts
open Coproducts hasCoproducts

distr : ∀{X Y Z} → Hom (X × (Y + Z)) (X × Y + X × Z) 
distr = {!!}

isDist : Distributive hasProducts hasCoproducts I hasInitial
isDist = record { distribute = λ {A B C} →
                               iso {!!} 
                                   {!!} 
                                   {!!} ; 
                  nullify = {!!} }

