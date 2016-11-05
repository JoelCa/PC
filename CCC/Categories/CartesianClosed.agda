
open import Categories
open import Categories.Products
open import Categories.Terminal

module Categories.CartesianClosed {a}{b}{C : Cat {a}{b}}
                                        (hasProducts : Products C)
                                        (T : Cat.Obj C)
                                        (hasTerminal : Terminal C T)
                                        where

open import Library hiding (_×_;curry;uncurry;_+_)

open Cat C
open import Categories.Products
open Products hasProducts
open import Categories.Products.Properties hasProducts using (comp-pair ; iden-comp-pair)


record CCC : Set (a ⊔ b) where
  infix 4 _⇒_
  field
     _⇒_ : Obj → Obj → Obj
     curry : ∀{X Y Z} → Hom (X × Y) Z → Hom X (Y ⇒ Z)
     uncurry : ∀{X Y Z} → Hom X (Y ⇒ Z) → Hom (X × Y) Z
     lawcurry1 : ∀{X Y Z}{f : Hom (X × Y) Z} → uncurry (curry f) ≅ f
     lawcurry2 : ∀{X Y Z}{f : Hom X (Y ⇒ Z)} → curry (uncurry f) ≅ f
     nat-curry : ∀{X X' Y Z Z'} → {f : Hom X' X}{h : Hom Z Z'}{x : Hom (X × Y) Z}
               →  curry (h ∙ uncurry iden) ∙ curry x ∙ f ≅ curry (h ∙ x ∙ pair f iden)

  apply : ∀{Y Z} → Hom ((Y ⇒ Z) × Y) Z
  apply = uncurry iden    

  map⇒ : ∀{X Y Z} → Hom X Z → Hom (Y ⇒ X) (Y ⇒ Z)
  map⇒ f = curry (f ∙ apply)


  curry-prop₁ : ∀{X X' Y Z} → {g : Hom X' X}{f : Hom (X × Y) Z} →
               curry f ∙ g ≅ curry (f ∙ pair g iden)
  curry-prop₁ {g = g} {f} = proof curry f ∙ g
                           ≅⟨ sym idl ⟩
                           iden ∙ curry f ∙ g
                           ≅⟨ cong (λ x → x ∙ curry f ∙ g) (sym lawcurry2) ⟩
                           curry (uncurry iden) ∙  curry f ∙ g
                           ≅⟨ cong (λ x → curry x ∙ curry f ∙ g) (sym idl) ⟩
                           curry (iden ∙ uncurry iden) ∙  curry f ∙ g
                           ≅⟨ nat-curry ⟩
                           curry (iden ∙ f ∙ pair g iden)
                           ≅⟨ cong (λ x → curry x) idl ⟩
                           curry (f ∙ pair g iden) ∎


  curry-prop₂ : ∀{X Y Z} {f : Hom X (Y ⇒ Z)} → f ≅ curry (apply ∙ pair f iden)
  curry-prop₂ {f = f} = sym (proof curry (apply ∙ pair f iden)
                            ≅⟨ sym curry-prop₁ ⟩
                            curry apply ∙ f
                            ≅⟨ cong (λ x → x ∙ f) lawcurry2 ⟩
                            iden ∙ f
                            ≅⟨ idl ⟩
                            f ∎)

  uncurry-prop₁ : ∀{X Y Z} {f : Hom X (Y ⇒ Z)} → uncurry f ≅ apply ∙ pair f iden
  uncurry-prop₁ {f = f} = proof uncurry f
                          ≅⟨ cong (λ x → uncurry x) curry-prop₂ ⟩
                          uncurry (curry (apply ∙ pair f iden))
                          ≅⟨ lawcurry1 ⟩
                          apply ∙ pair f iden ∎
                          

  uncurry-prop₂ : ∀{X X' Y Y' Z} {f : Hom X (Y ⇒ Z)} {g : Hom X' X} {h : Hom Y' Y}
                  → uncurry f ∙ pair g h ≅ apply ∙ pair (f ∙ g) h
  uncurry-prop₂ {f = f} {g} {h} = proof
                                  uncurry f ∙ pair g h
                                  ≅⟨ cong (λ x → x ∙ pair g h) uncurry-prop₁ ⟩
                                  (apply ∙ pair f iden) ∙ pair g h
                                  ≅⟨ ass ⟩
                                  apply ∙ (pair f iden ∙ pair g h)
                                  ≅⟨ cong (λ x → apply ∙ x) (sym comp-pair) ⟩
                                  apply ∙ pair (f ∙ g) (iden ∙ h)
                                  ≅⟨ cong (λ x → apply ∙ pair (f ∙ g) x) idl ⟩
                                  apply ∙ pair (f ∙ g) h ∎


  curry-prop₃ : ∀{X Y Z} {f : Hom (X × Y) Z} →  apply ∙ pair (curry f) iden ≅ f
  curry-prop₃ {f = f} = proof apply ∙ pair (curry f) iden 
                        ≅⟨ sym uncurry-prop₁ ⟩
                        uncurry (curry f) 
                        ≅⟨ lawcurry1 ⟩
                        f ∎

  nat-uncurry : ∀{X X' Y Z Z'} → {f : Hom X' X}{h : Hom Z Z'}{x : Hom X (Y ⇒ Z)}
                →  h ∙ uncurry (x) ∙ pair f iden  ≅ uncurry (map⇒ h ∙ x ∙ f)
  nat-uncurry {f = f} {h} {x} = sym (proof
                                    uncurry (map⇒ h ∙ x ∙ f)
                                    ≅⟨ cong (λ w → uncurry w) curry-prop₁ ⟩
                                    uncurry (curry ((h ∙ apply) ∙ pair (x ∙ f) iden))
                                    ≅⟨ lawcurry1 ⟩
                                    (h ∙ apply) ∙ pair (x ∙ f) iden
                                    ≅⟨ ass ⟩
                                    h ∙ (apply ∙ pair (x ∙ f) iden)
                                    ≅⟨ cong (λ w → h ∙ (apply ∙ w)) iden-comp-pair ⟩
                                    h ∙ (apply ∙ (pair x iden ∙ pair f iden))
                                    ≅⟨ cong (λ w → h ∙ w) (sym ass) ⟩
                                    h ∙ ((apply ∙ pair x iden) ∙ pair f iden)
                                    ≅⟨ cong (λ w → h ∙ (w ∙ pair f iden)) (sym uncurry-prop₁) ⟩
                                    h ∙ uncurry x ∙ pair f iden ∎)
