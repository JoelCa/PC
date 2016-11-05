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

h : ∀{X Y Z} → Hom (Y + Z) (X ⇒ (X × Y + X × Z))
h = [ curry (inl ∙ ⟨ π₂ , π₁ ⟩) , curry (inr ∙ ⟨ π₂ , π₁ ⟩) ]

distr : ∀{X Y Z} → Hom (X × (Y + Z)) (X × Y + X × Z)
distr {X} {Y} {Z} = uncurry h ∙ ⟨ π₂ , π₁ ⟩


lema₁ : ∀{X X' Y Z W W'}{f : Hom X (Y ⇒ Z)}{g : Hom X' (Y ⇒ Z)}{h : Hom W (X + X')}
       {e : Hom W (Y ⇒ Z)}
       → ([ f , g ] ∙ h ≅ e)
       → ((pair [ f , g ] iden) ∙ ⟨ π₂ , π₁ ⟩) ∙ pair iden h ≅
         pair e iden ∙ ⟨ π₂ {W'} {W}, π₁ ⟩
lema₁ {f = f} {g} {h} {e} prop = proof
                                 ((pair [ f , g ] iden) ∙ ⟨ π₂ , π₁ ⟩) ∙ pair iden h
                                 ≅⟨ ass ⟩
                                 (pair [ f , g ] iden) ∙ ⟨ π₂ , π₁ ⟩ ∙ pair iden h
                                 ≅⟨ cong (λ x → pair [ f , g ] iden ∙ x) swap-pair ⟩
                                 pair [ f , g ] iden ∙ (pair h iden ∙ ⟨ π₂ , π₁ ⟩)
                                 ≅⟨ sym ass ⟩
                                 (pair [ f , g ] iden ∙ pair h iden) ∙ ⟨ π₂ , π₁ ⟩
                                 ≅⟨ cong (λ x → x ∙ ⟨ π₂ , π₁ ⟩) (sym comp-pair) ⟩
                                 pair ([ f , g ] ∙ h) (iden ∙ iden) ∙ ⟨ π₂ , π₁ ⟩
                                 ≅⟨ cong₂ (λ x y → pair x y ∙ ⟨ π₂ , π₁ ⟩) prop idl ⟩
                                 pair e iden ∙ ⟨ π₂ , π₁ ⟩ ∎

lema₂ : ∀{X Y Z Z'}{f : Hom Z Z'}{g : Hom (X × Y) Z}{h : Hom Z (X × Y)}
       → g ∙ h ≅ iden
       → apply ∙ ((pair (curry (f ∙ g)) iden) ∙ h) ≅ f
lema₂ {f = f} {g} {h} prop = proof
                               apply ∙ ((pair (curry (f ∙ g)) iden) ∙ h)
                               ≅⟨ sym ass ⟩
                               (apply ∙ (pair (curry (f ∙ g)) iden)) ∙ h
                               ≅⟨ cong (λ x → x ∙ h) curry-prop₃ ⟩
                               (f ∙ g) ∙ h
                               ≅⟨ ass ⟩
                               f ∙ (g ∙ h)
                               ≅⟨ cong (λ x → f ∙ x) prop ⟩
                               f ∙ iden
                               ≅⟨ idr ⟩
                               f ∎



lema₃ : ∀{X X' Y Z}{f : Hom X (Y ⇒ Z)}{g : Hom (Y × X') Z}{h : Hom X' X}
       → (f ∙ h ≅ curry (g ∙ ⟨ π₂ , π₁ ⟩))
       → (uncurry f ∙ ⟨ π₂ , π₁ ⟩) ∙ pair iden h ≅ g
lema₃ {f = f} {g} {h} prop = proof
                               (uncurry f ∙ ⟨ π₂ , π₁ ⟩) ∙ pair iden h
                               ≅⟨ ass ⟩
                               uncurry f ∙ (⟨ π₂ , π₁ ⟩ ∙ pair iden h)
                               ≅⟨ cong (λ x → uncurry f ∙ x) swap-pair ⟩
                               uncurry f ∙ (pair h iden ∙ ⟨ π₂ , π₁ ⟩)
                               ≅⟨ sym ass ⟩
                               (uncurry f ∙ pair h iden) ∙ ⟨ π₂ , π₁ ⟩
                               ≅⟨ cong (λ x → x ∙ ⟨ π₂ , π₁ ⟩) uncurry-prop₂ ⟩
                               (apply ∙ pair (f ∙ h) iden) ∙ ⟨ π₂ , π₁ ⟩
                               ≅⟨ cong (λ x → (apply ∙ pair x iden) ∙ ⟨ π₂ , π₁ ⟩)
                                       prop ⟩
                               (apply ∙ pair (curry (g ∙ ⟨ π₂ , π₁ ⟩)) iden) ∙ ⟨ π₂ , π₁ ⟩
                               ≅⟨ cong (λ x → x ∙ ⟨ π₂ , π₁ ⟩) curry-prop₃ ⟩
                               (g ∙ ⟨ π₂ , π₁ ⟩) ∙ ⟨ π₂ , π₁ ⟩
                               ≅⟨ ass ⟩
                               g ∙ (⟨ π₂ , π₁ ⟩ ∙ ⟨ π₂ , π₁ ⟩)
                               ≅⟨ cong (λ x → g ∙ x) double-swap ⟩
                               g ∙ iden
                               ≅⟨ idr ⟩
                               g ∎


--NO esta congr
distr-undistr : ∀{X Y Z} → (distr {X} {Y} {Z}) ∙ undistr ≅ iden {X × Y + X × Z}
distr-undistr {X} {Y} {Z} = proof
                              distr ∙ undistr
                              ≅⟨ co-fusion ⟩
                              [ (uncurry h ∙ ⟨ π₂ , π₁ ⟩) ∙ pair iden inl ,
                                 (uncurry h ∙ ⟨ π₂ , π₁ ⟩) ∙ pair iden inr ]
                              ≅⟨ cong₂ (λ x y → [ x , y ]) (lema₃ co-law1) (lema₃ co-law2) ⟩
                              [ inl , inr ]
                              ≅⟨ copro-iden ⟩
                              iden ∎



isDist : Distributive 
isDist = record { distribute = λ {X Y Z} →
                                 iso (distr {X} {Y} {Z})
                                     {!!} 
                                     {!!} ; 
                  nullify = {!!} }
