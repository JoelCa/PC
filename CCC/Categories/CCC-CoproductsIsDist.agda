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

open Products hasProducts
open Coproducts hasCoproducts renaming (law1 to co-law1 ; law2 to co-law2) 
open import Categories.Coproducts.Properties hasCoproducts renaming (fusion to co-fusion)
open import Categories.Products.Properties hasProducts
open Cat C
open CCC hasProducts T hasTerminal isCCC
open Initial hasInitial


h : ∀{X Y Z} → Hom (Y + Z) (X ⇒ (X × Y + X × Z))
h = [ curry (inl ∙ ⟨ π₂ , π₁ ⟩) , curry (inr ∙ ⟨ π₂ , π₁ ⟩) ]

distr : ∀{X Y Z} → Hom (X × (Y + Z)) (X × Y + X × Z)
distr {X} {Y} {Z} = uncurry h ∙ ⟨ π₂ , π₁ ⟩


lema₁ : ∀{X X' Y Z}{f : Hom X (Y ⇒ Z)}{g : Hom (Y × X') Z}{h : Hom X' X}
       → (f ∙ h ≅ curry (g ∙ ⟨ π₂ , π₁ ⟩))
       → (uncurry f ∙ ⟨ π₂ , π₁ ⟩) ∙ pair iden h ≅ g
lema₁ {f = f} {g} {h} prop = proof
                               (uncurry f ∙ ⟨ π₂ , π₁ ⟩) ∙ pair iden h
                               ≅⟨ ass ⟩
                               uncurry f ∙ (⟨ π₂ , π₁ ⟩ ∙ pair iden h)
                               ≅⟨ cong (λ x → uncurry f ∙ x) swap-pair ⟩
                               uncurry f ∙ (pair h iden ∙ ⟨ π₂ , π₁ ⟩)
                               ≅⟨ sym ass ⟩
                               (uncurry f ∙ pair h iden) ∙ ⟨ π₂ , π₁ ⟩
                               ≅⟨ cong (λ x → x ∙ ⟨ π₂ , π₁ ⟩) uncurry-prop₄ ⟩
                               uncurry (f ∙ h) ∙ ⟨ π₂ , π₁ ⟩
                               ≅⟨ cong (λ x → uncurry x ∙ ⟨ π₂ , π₁ ⟩) prop ⟩
                               uncurry (curry (g ∙ ⟨ π₂ , π₁ ⟩)) ∙ ⟨ π₂ , π₁ ⟩
                               ≅⟨ cong (λ x → x ∙ ⟨ π₂ , π₁ ⟩) lawcurry1 ⟩
                               (g ∙ ⟨ π₂ , π₁ ⟩) ∙ ⟨ π₂ , π₁ ⟩
                               ≅⟨ ass ⟩
                               g ∙ (⟨ π₂ , π₁ ⟩ ∙ ⟨ π₂ , π₁ ⟩)
                               ≅⟨ cong (λ x → g ∙ x) double-swap ⟩
                               g ∙ iden
                               ≅⟨ idr ⟩
                               g ∎


lema₂ : ∀{X Y Z Z'}{f : Hom (Y × X) Z}{g : Hom Z (Y × Z')}{h : Hom X Z'}
        → g ∙ f ≅ pair iden h
        → map⇒ g ∙ curry (f ∙ ⟨ π₂ , π₁ ⟩) ≅ curry ⟨ π₂ , π₁ ⟩ ∙ h
lema₂ {f = f} {g} {h} prop = proof
                               map⇒ g ∙ curry (f ∙ ⟨ π₂ , π₁ ⟩)
                               ≅⟨ curry-prop₄ ⟩
                               curry (g ∙ f ∙ ⟨ π₂ , π₁ ⟩)
                               ≅⟨ cong (λ x → curry x) (sym ass) ⟩
                               curry ((g ∙ f) ∙ ⟨ π₂ , π₁ ⟩)
                               ≅⟨ cong (λ x → curry (x ∙ ⟨ π₂ , π₁ ⟩)) prop ⟩
                               curry (pair iden h ∙ ⟨ π₂ , π₁ ⟩)
                               ≅⟨ cong (λ x → curry x) (sym swap-pair) ⟩
                               curry (⟨ π₂ , π₁ ⟩ ∙ pair h iden)
                               ≅⟨ sym curry-prop₁ ⟩
                               curry ⟨ π₂ , π₁ ⟩ ∙ h ∎


-- NO utilizo cong₂ por hace al tipe-checker más lento
lema₃ : ∀{X Y Z} → map⇒ (undistr {X} {Y} {Z}) ∙ h ≅ curry ⟨ π₂ , π₁ ⟩
lema₃ = proof
          map⇒ undistr ∙ h
          ≅⟨ co-fusion ⟩
          [ map⇒ undistr ∙ curry (inl ∙ ⟨ π₂ , π₁ ⟩) ,
            map⇒ undistr ∙ curry (inr ∙ ⟨ π₂ , π₁ ⟩) ]
          ≅⟨ cong (λ x → [ x , map⇒ undistr ∙ curry (inr ∙ ⟨ π₂ , π₁ ⟩) ]) (lema₂ co-law1) ⟩
          [ curry ⟨ π₂ , π₁ ⟩ ∙ inl ,
            map⇒ undistr ∙ curry (inr ∙ ⟨ π₂ , π₁ ⟩) ]
          ≅⟨ cong (λ x → [ curry ⟨ π₂ , π₁ ⟩ ∙ inl , x ]) (lema₂ co-law2) ⟩
          [ curry ⟨ π₂ , π₁ ⟩ ∙ inl , curry ⟨ π₂ , π₁ ⟩ ∙ inr ]
          ≅⟨ sym co-fusion ⟩
          curry ⟨ π₂ , π₁ ⟩ ∙ [ inl , inr ]
          ≅⟨ cong (λ x → curry ⟨ π₂ , π₁ ⟩ ∙ x) copro-iden ⟩
          curry ⟨ π₂ , π₁ ⟩ ∙ iden
          ≅⟨ idr ⟩
          curry ⟨ π₂ , π₁ ⟩ ∎


--NO esta congr
-- NO utilizo cong₂ por hace al tipe-checker más lento
distr-undistr : ∀{X Y Z} → (distr {X} {Y} {Z}) ∙ undistr ≅ iden {X × Y + X × Z}
distr-undistr = proof
                distr ∙ undistr
                ≅⟨ co-fusion ⟩
                [ (uncurry h ∙ ⟨ π₂ , π₁ ⟩) ∙ pair iden inl ,
                  (uncurry h ∙ ⟨ π₂ , π₁ ⟩) ∙ pair iden inr ]
                ≅⟨ cong (λ x → [ x , (uncurry h ∙ ⟨ π₂ , π₁ ⟩) ∙ pair iden inr ])
                        (lema₁ co-law1) ⟩
                [ inl , (uncurry h ∙ ⟨ π₂ , π₁ ⟩) ∙ pair iden inr ]
                ≅⟨ cong (λ x → [ inl , x ]) (lema₁ co-law2) ⟩
                [ inl , inr ]
                ≅⟨ copro-iden ⟩
                iden ∎


undistr-distr : ∀{X Y Z} → undistr ∙ (distr {X} {Y} {Z}) ≅ iden {X × (Y + Z)}
undistr-distr = proof
                  undistr ∙ uncurry h ∙ ⟨ π₂ , π₁ ⟩
                  ≅⟨ sym ass ⟩
                  (undistr ∙ uncurry h) ∙ ⟨ π₂ , π₁ ⟩
                  ≅⟨ cong (λ x → x ∙ ⟨ π₂ , π₁ ⟩) uncurry-prop₃ ⟩
                  uncurry (map⇒ undistr ∙ h) ∙ ⟨ π₂ , π₁ ⟩
                  ≅⟨ cong (λ x → uncurry x ∙ ⟨ π₂ , π₁ ⟩) lema₃ ⟩
                  uncurry (curry  ⟨ π₂ , π₁ ⟩) ∙  ⟨ π₂ , π₁ ⟩
                  ≅⟨ cong (λ x → x ∙  ⟨ π₂ , π₁ ⟩) lawcurry1 ⟩
                  ⟨ π₂ , π₁ ⟩ ∙ ⟨ π₂ , π₁ ⟩
                  ≅⟨ double-swap ⟩
                  iden ∎


inv-unnull : ∀{X} → Hom (X × I) I
inv-unnull = uncurry i ∙ ⟨ π₂ , π₁ ⟩

isDist : Distributive 
isDist = record { distribute = λ {X Y Z} →
                                 iso (distr {X} {Y} {Z})
                                     undistr-distr 
                                     distr-undistr ; 
                  nullify = {!!} }
