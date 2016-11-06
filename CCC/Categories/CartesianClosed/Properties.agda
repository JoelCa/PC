
open import Categories
open import Categories.Products
open import Categories.Coproducts
open import Categories.Terminal
open import Categories.Initial
open import Categories.CartesianClosed


module Categories.CartesianClosed.Properties {l m}{C : Cat {l}{m}}
                                             {T : Cat.Obj C}
                                             {hasProducts : Products C}
                                             {hasTerminal : Terminal C T}
                                             (isCCC : CCC hasProducts T hasTerminal)
                                             where

open import Library hiding (_×_ ; curry ; uncurry ; _+_)
open Cat C
open CCC hasProducts T hasTerminal isCCC
open Products hasProducts
open import Categories.Products.Properties hasProducts using (comp-pair ;
                                                             iden-comp-pair;
                                                             iden-pair)

map⇒iden : ∀{X Y} → map⇒ (iden {X}) ≅ iden {Y ⇒ X}
map⇒iden = proof
           curry (iden ∙ apply)
           ≅⟨ cong (λ x → curry x) idl ⟩
           curry apply
           ≅⟨ lawcurry2 ⟩
           iden ∎

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

curry-prop₄ : ∀{X Y Z Z'}{f : Hom (X × Y) Z}{g : Hom Z Z'}
             →  map⇒ g ∙ curry f ≅ curry (g ∙ f)
curry-prop₄ {f = f} {g} = proof
                          curry (g ∙ apply) ∙ curry f
                          ≅⟨ sym idr ⟩
                          (curry (g ∙ apply) ∙ curry f) ∙ iden
                          ≅⟨ ass ⟩
                          curry (g ∙ apply) ∙ (curry f ∙ iden)
                          ≅⟨ nat-curry ⟩
                          curry (g ∙ f ∙ pair iden iden)
                          ≅⟨ cong (λ x → curry (g ∙ f ∙ x)) iden-pair ⟩
                          curry (g ∙ f ∙ iden)
                          ≅⟨ cong (λ x → curry (g ∙ x)) idr ⟩
                          curry (g ∙ f) ∎

--Esta bien?
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


uncurry-prop₃ : ∀{X Y Z Z'} {f : Hom X (Y ⇒ Z)} {g : Hom Z Z'}
                → g ∙ uncurry f ≅ uncurry (map⇒ g ∙ f)
uncurry-prop₃ {f = f} {g} = proof
                            g ∙ uncurry f
                            ≅⟨ sym idr ⟩
                            (g ∙ uncurry f) ∙ iden
                            ≅⟨ cong (λ x → (g ∙ uncurry f) ∙ x) (sym iden-pair) ⟩
                            (g ∙ uncurry f) ∙ pair iden iden
                            ≅⟨ ass ⟩
                            g ∙ uncurry f ∙ pair iden iden
                            ≅⟨ nat-uncurry ⟩
                            uncurry (map⇒ g ∙ f ∙ iden)
                            ≅⟨ cong (λ x → uncurry (map⇒ g ∙ x)) idr ⟩
                            uncurry (map⇒ g ∙ f) ∎


uncurry-prop₄ : ∀{X X' Y Z} {f : Hom X (Y ⇒ Z)} {g : Hom X' X}
                → uncurry f ∙ pair g iden ≅ uncurry (f ∙ g)
uncurry-prop₄ {f = f} {g} = proof
                              uncurry f ∙ pair g iden
                              ≅⟨ sym idl ⟩
                              iden ∙ uncurry f ∙ pair g iden
                              ≅⟨ nat-uncurry ⟩
                              uncurry (map⇒ iden ∙ f ∙ g)
                              ≅⟨ cong (λ x → uncurry (x ∙ f ∙ g)) map⇒iden ⟩
                              uncurry (iden ∙ f ∙ g)
                              ≅⟨ cong (λ x → uncurry x) idl ⟩
                              uncurry (f ∙ g) ∎  

