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
open import Categories.Coproducts.Properties hasCoproducts renaming (fusion to co-fusion)
open import Categories.Products.Properties hasProducts

--prueba : ∀{X Y Z} {C : CCC} → Hom (X × Y) Z → Hom X (_⇒_ C Y Z)
--prueba {X} {Y} {Z} {C} =  curry C

distr : ∀{X Y Z} {C : CCC} → Hom (X × (Y + Z)) (X × Y + X × Z)
distr {X} {Y} {Z} {C} = let open CCC C in
                        uncurry ([ curry (inl ∙ ⟨ π₂ , π₁ ⟩) , curry (inr ∙ ⟨ π₂ , π₁ ⟩) ])
                          ∙ ⟨ π₂ , π₁ ⟩

distri₁ : ∀{X Y Z} {C : CCC} → (distr {X} {Y} {Z} {C}) ∙ undistr ≅ iden {X × Y + X × Z}
distri₁ {X} {Y} {Z} {C = C} = let open CCC C
                                  h = [ curry (inl ∙ ⟨ π₂ , π₁ ⟩) , curry (inr ∙ ⟨ π₂ , π₁ ⟩) ]
                              in
                              proof distr {X} {Y} {Z} {C} ∙ undistr
                              ≅⟨ cong (λ x → (x ∙ ⟨ π₂ , π₁ ⟩) ∙ undistr) uncurry-prop ⟩
                              ((apply ∙ pair h iden) ∙ ⟨ π₂ , π₁ ⟩) ∙ undistr
                              ≅⟨ cong (λ x → x ∙ undistr) ass ⟩
                              (apply ∙ (pair h iden ∙ ⟨ π₂ , π₁ ⟩)) ∙ undistr
                              ≅⟨ cong (λ x → (apply ∙ x) ∙ undistr) fusion-pair ⟩
                              (apply ∙ ⟨ h ∙ π₂ , iden ∙ π₁ ⟩) ∙ undistr
                              ≅⟨ cong (λ x → (apply ∙ ⟨ h ∙ π₂ , x ⟩) ∙ undistr) idl ⟩
                              (apply ∙ ⟨ h ∙ π₂ , π₁ ⟩) ∙ undistr
                              ≅⟨ ass ⟩
                              apply ∙ (⟨ h ∙ π₂ , π₁ ⟩ ∙ undistr)
                              ≅⟨ cong (λ x → apply ∙ x) co-fusion ⟩
                              apply ∙ [ ⟨ h ∙ π₂ , π₁ ⟩ ∙ pair iden  inl ,
                                        ⟨ h ∙ π₂ , π₁ ⟩ ∙ pair iden  inr ]
                              ≅⟨ cong₂ (λ x y → apply ∙ [ x , y ]) fusion fusion ⟩
                              apply ∙ [ ⟨ (h ∙ π₂) ∙ pair iden  inl , π₁ ∙ pair iden  inl ⟩ ,
                                        ⟨ (h ∙ π₂) ∙ pair iden  inr , π₁ ∙ pair iden  inr ⟩ ]
                              ≅⟨ cong₂ (λ x y → apply ∙ [ ⟨ x , π₁ ∙ pair iden  inl ⟩ ,
                                                          ⟨ y , π₁ ∙ pair iden  inr ⟩ ]) ass ass ⟩
                              apply ∙ [ ⟨ h ∙ (π₂ ∙ pair iden  inl) ,  π₁ ∙ pair iden  inl ⟩ ,
                                        ⟨ h ∙ (π₂ ∙ pair iden  inr) , π₁ ∙ pair iden  inr ⟩ ]
                              ≅⟨ cong₂ (λ x y → apply ∙ [ ⟨ h ∙ x ,  π₁ ∙ pair iden  inl ⟩ ,
                                                          ⟨ h ∙ y ,  π₁ ∙ pair iden  inr ⟩ ]) {!π₂-pair!} {!π₂-pair!} ⟩
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
--apply ∙ [ ⟨ x , π₁ ∙ pair iden  inl ⟩ , ⟨ y , π₁ ∙ pair iden  inr ⟩ ]

-- apply ∙ [ ⟨ x , π₁ ∙ pair iden  inl ⟩ ,
--                                                           ⟨ y , π₁ ∙ pair iden  inr ⟩ ]

isDist : {C : CCC} → Distributive 
isDist {C} = let open CCC C in
             record { distribute = λ {X Y Z} →
                                   iso (distr {X} {Y} {Z} {C})
                                       {!!} 
                                       {!!} ; 
                      nullify = {!!} }

