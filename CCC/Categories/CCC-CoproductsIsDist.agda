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

open import Library hiding (_×_ ; _+_ ; curry ; uncurry)
open import Categories.Distributive hasProducts hasCoproducts I hasInitial
open import Categories.CartesianClosed hasProducts T hasTerminal

open Cat C
open Products hasProducts
open Coproducts hasCoproducts

--prueba : ∀{X Y Z} {C : CCC} → Hom (X × Y) Z → Hom X (_⇒_ C Y Z)
--prueba {X} {Y} {Z} {C} =  curry C

distr : ∀{X Y Z} {C : CCC} → Hom (X × (Y + Z)) (X × Y + X × Z)
distr {X} {Y} {Z} {C} = let open CCC C in
                        uncurry ([ curry (inl ∙ ⟨ π₂ , π₁ ⟩) , curry (inr ∙ ⟨ π₂ , π₁ ⟩) ])
                          ∙ ⟨ π₂ , π₁ ⟩

distri₁ : {C : CCC} → distr ∙ undistr ≅ iden
distri₁ {C} = let open CCC C in
              proof {!!}
                ≅⟨ {!!} ⟩
                {!!}
                ≅⟨ {!!} ⟩
                {!!}
                ≅⟨ {!!} ⟩
                {!!}
                ≅⟨ {!!} ⟩
                {!!}
                ≅⟨ {!!} ⟩
                {!!}
                ≅⟨ {!!} ⟩
                {!!}
                ≅⟨ {!!} ⟩
                {!!}
                ≅⟨ {!!} ⟩
                {!!} ∎


isDist : {C : CCC} → Distributive 
isDist {C} = let open CCC C in
             record { distribute = λ {X Y Z} →
                                   iso (distr {X} {Y} {Z} {C})
                                       {!!} 
                                       {!!} ; 
                      nullify = {!!} }

