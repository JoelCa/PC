open import Categories
open import Categories.Products
open import Categories.Coproducts
open import Categories.Terminal
open import Categories.Initial
open import Categories.CartesianClosed

module Categories.CCC-CoproductsIsDist {a}{b}{C : Cat {a}{b}}
                                       {T : Cat.Obj C}
                                       {I : Cat.Obj C}
                                       (hasProducts : Products C)
                                       (hasCoproducts : Coproducts C)           
                                       (hasTerminal : Terminal C T)
                                       (hasInitial : Initial C I)
                                       (isCCC : CCC hasProducts T hasTerminal)
                                       where

open import Library hiding (_×_ ; _+_ ; curry ; uncurry)
open import Categories.Distributive hasProducts hasCoproducts I hasInitial

open Cat C
open Products hasProducts
open Coproducts hasCoproducts renaming (law1 to co-law1 ; law2 to co-law2) 
open import Categories.Coproducts.Properties hasCoproducts renaming (fusion to co-fusion)
open import Categories.Products.Properties hasProducts
open CCC isCCC

distr : ∀{X Y Z} → Hom (X × (Y + Z)) (X × Y + X × Z)
distr {X} {Y} {Z} = uncurry ([ curry (inl ∙ ⟨ π₂ , π₁ ⟩) , curry (inr ∙ ⟨ π₂ , π₁ ⟩) ])
                          ∙ ⟨ π₂ , π₁ ⟩

h : ∀{X Y Z} → Hom (Y + Z) (X ⇒ (X × Y + X × Z))
h = [ curry (inl ∙ ⟨ π₂ , π₁ ⟩) , curry (inr ∙ ⟨ π₂ , π₁ ⟩) ]

distri₁ : ∀{X Y Z} → (distr {X} {Y} {Z}) ∙ undistr ≅ apply ∙ [ ⟨ h ∙ π₂ , π₁ ⟩ ∙ pair iden  inl , ⟨ h ∙ π₂ , π₁ ⟩ ∙ pair iden  inr ]
distri₁ {X} {Y} {Z} = proof distr {X} {Y} {Z} ∙ undistr
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
                                      ⟨ h ∙ π₂ , π₁ ⟩ ∙ pair iden  inr ] ∎

distri₂ : ⟨ h ∙ π₂ , π₁ ⟩ ∙ pair iden  inl ≅ curry (inl ∙ ⟨ π₂ , π₁ ⟩) ∙ π₂
distri₂ = proof
          ⟨ h ∙ π₂ , π₁ ⟩ ∙ pair iden  inl
          ≅⟨ fusion ⟩
          ⟨ (h ∙ π₂) ∙ pair iden  inl , π₁ ∙ pair iden  inl ⟩
          ≅⟨ cong (λ x → ⟨ x , π₁ ∙ pair iden  inl ⟩ ass ⟩
          ⟨ h ∙ (π₂ ∙ pair iden  inl) ,  π₁ ∙ pair iden  inl ⟩
          ≅⟨ cong₂ (λ x y → [ ⟨ h ∙ x ,  π₁ ∙ pair iden  inl ⟩ ,
                              ⟨ h ∙ y ,  π₁ ∙ pair iden  inr ⟩ ]) π₂-pair2 π₂-pair2 ⟩
          [ ⟨ h ∙ (inl ∙ π₂) , π₁ ∙ pair iden  inl ⟩ , 
            ⟨ h ∙ (inr ∙ π₂) , π₁ ∙ pair iden  inr ⟩ ]
          ≅⟨ cong₂ (λ x y →  [ ⟨ x , π₁ ∙ pair iden  inl ⟩ ,
                                ⟨ y , π₁ ∙ pair iden  inr ⟩ ]) (sym ass) (sym ass) ⟩
          [ ⟨ (h ∙ inl) ∙ π₂ , π₁ ∙ pair iden  inl ⟩ , 
            ⟨ (h ∙ inr) ∙ π₂ , π₁ ∙ pair iden  inr ⟩ ]
          ≅⟨ cong₂ (λ x y → [ ⟨ x ∙ π₂ , π₁ ∙ pair iden  inl ⟩ , 
                              ⟨ y ∙ π₂ , π₁ ∙ pair iden  inr ⟩ ]) co-law1 co-law2 ⟩
          [ ⟨ curry (inl ∙ ⟨ π₂ , π₁ ⟩) ∙ π₂ , π₁ ∙ pair iden  inl ⟩ , 
            ⟨ curry (inr ∙ ⟨ π₂ , π₁ ⟩) ∙ π₂ , π₁ ∙ pair iden  inr ⟩ ] ∎


distri-final : ∀{X Y Z} → (distr {X} {Y} {Z}) ∙ undistr ≅ iden {X × Y + X × Z}
distri-final {X} {Y} {Z} = {!!}
-- proof distr {X} {Y} {Z} {C} ∙ undistr
--                               ≅⟨ cong (λ x → (x ∙ ⟨ π₂ , π₁ ⟩) ∙ undistr) uncurry-prop ⟩
--                               ((apply ∙ pair h iden) ∙ ⟨ π₂ , π₁ ⟩) ∙ undistr
--                               ≅⟨ cong (λ x → x ∙ undistr) ass ⟩
--                               (apply ∙ (pair h iden ∙ ⟨ π₂ , π₁ ⟩)) ∙ undistr
--                               ≅⟨ cong (λ x → (apply ∙ x) ∙ undistr) fusion-pair ⟩
--                               (apply ∙ ⟨ h ∙ π₂ , iden ∙ π₁ ⟩) ∙ undistr
--                               ≅⟨ cong (λ x → (apply ∙ ⟨ h ∙ π₂ , x ⟩) ∙ undistr) idl ⟩
--                               (apply ∙ ⟨ h ∙ π₂ , π₁ ⟩) ∙ undistr
--                               ≅⟨ ass ⟩
--                               apply ∙ (⟨ h ∙ π₂ , π₁ ⟩ ∙ undistr)
--                               ≅⟨ congr co-fusion ⟩
--                               apply ∙ [ ⟨ h ∙ π₂ , π₁ ⟩ ∙ pair iden  inl ,
--                                         ⟨ h ∙ π₂ , π₁ ⟩ ∙ pair iden  inr ]
--                               ≅⟨ cong₂ (λ x y → apply ∙ [ x , y ]) fusion fusion ⟩
--                               apply ∙ [ ⟨ (h ∙ π₂) ∙ pair iden  inl , π₁ ∙ pair iden  inl ⟩ ,
--                                         ⟨ (h ∙ π₂) ∙ pair iden  inr , π₁ ∙ pair iden  inr ⟩ ]
--                               ≅⟨ cong₂ (λ x y → apply ∙ [ ⟨ x , π₁ ∙ pair iden  inl ⟩ ,
--                                                           ⟨ y , π₁ ∙ pair iden  inr ⟩ ]) ass ass ⟩
--                               apply ∙ [ ⟨ h ∙ (π₂ ∙ pair iden  inl) ,  π₁ ∙ pair iden  inl ⟩ ,
--                                         ⟨ h ∙ (π₂ ∙ pair iden  inr) , π₁ ∙ pair iden  inr ⟩ ]
--                               ≅⟨ cong₂ (λ x y → apply ∙ [ ⟨ h ∙ x ,  π₁ ∙ pair iden  inl ⟩ ,
--                                                           ⟨ h ∙ y ,  π₁ ∙ pair iden  inr ⟩ ]) π₂-pair2 π₂-pair2 ⟩
--                               apply ∙ [ ⟨ h ∙ (inl ∙ π₂) , π₁ ∙ pair iden  inl ⟩ , 
--                                         ⟨ h ∙ (inr ∙ π₂) , π₁ ∙ pair iden  inr ⟩ ]
-- -----------------------
--                               ≅⟨ cong₂ (λ x y →  apply ∙ [ ⟨ x , π₁ ∙ pair iden  inl ⟩ ,
--                                                            ⟨ y , π₁ ∙ pair iden  inr ⟩ ]) (sym ass) (sym ass) ⟩
--                               apply ∙ [ ⟨ (h ∙ inl) ∙ π₂ , π₁ ∙ pair iden  inl ⟩ , 
--                                         ⟨ (h ∙ inr) ∙ π₂ , π₁ ∙ pair iden  inr ⟩ ]
--                               ≅⟨ cong₂ (λ x y → apply ∙ [ ⟨ x ∙ π₂ , π₁ ∙ pair iden  inl ⟩ , 
--                                                           ⟨ y ∙ π₂ , π₁ ∙ pair iden  inr ⟩ ]) co-law1 co-law2 ⟩
--                               apply ∙ [ ⟨ curry (inl ∙ ⟨ π₂ , π₁ ⟩) ∙ π₂ , π₁ ∙ pair iden  inl ⟩ , 
--                                         ⟨ curry (inr ∙ ⟨ π₂ , π₁ ⟩) ∙ π₂ , π₁ ∙ pair iden  inr ⟩ ]
--                               ≅⟨ cong₂ (λ x y → apply ∙ [ ⟨ curry (inl ∙ ⟨ π₂ , π₁ ⟩) ∙ π₂ , x ⟩ , ⟨ curry (inr ∙ ⟨ π₂ , π₁ ⟩) ∙ π₂ , y ⟩ ]) {!!} {!!} ⟩
--                               {!!}
--                               ≅⟨ {!!} ⟩
--                               {!!}
--                               ≅⟨ {!!} ⟩
--                               {!!}
--                               ≅⟨ {!!} ⟩
--                               {!!}
--                               ≅⟨ {!!} ⟩                              
--                               {!!} ∎

--apply ∙ [ ⟨ x ∙ π₂ , π₁ ∙ pair iden  inl ⟩ , ⟨ y ∙ π₂ , π₁ ∙ pair iden  inr ⟩ ]

isDist : Distributive 
isDist = record { distribute = λ {X Y Z} →
                                 iso (distr {X} {Y} {Z})
                                     {!!} 
                                     {!!} ; 
                  nullify = {!!} }

