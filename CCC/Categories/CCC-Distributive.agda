open import Categories
open import Categories.Products
open import Categories.Coproducts
open import Categories.Terminal
open import Categories.Initial
open import Categories.CartesianClosed

module Categories.CCC-Distributive {a}{b}{C : Cat {a}{b}}
                                   {T : Cat.Obj C}
                                   {I : Cat.Obj C}
                                   {hasProducts : Products C}
                                   {hasTerminal : Terminal C T}
                                   (hasCoproducts : Coproducts C)           
                                   (hasInitial : Initial C I)
                                   (isCCC : CCC hasProducts hasTerminal)
                                   where

open import Library hiding (_×_ ; _+_ ; curry ; uncurry ; swap)

open import Categories.Distributive hasProducts hasCoproducts I hasInitial
open import Categories.Coproducts.Properties hasCoproducts renaming (fusion to co-fusion)
open import Categories.Products.Properties hasProducts
open import Categories.CartesianClosed.Properties isCCC

open Products hasProducts
open Coproducts hasCoproducts renaming (law1 to co-law1 ; law2 to co-law2) 
open Cat C
open CCC hasProducts hasTerminal isCCC --isCCC --hasProducts hasTerminal isCCC
open Initial hasInitial
open ProductMorphisms hasProducts using (swap)


--Morfismo utilizado para definir "distr".
h : ∀{X Y Z} → Hom (Y + Z) (X ⇒ (X × Y + X × Z))
h = [ curry (inl ∙ swap) , curry (inr ∙ swap) ]


--Morfismo "inverso" de "undistr".
distr : ∀{X Y Z} → Hom (X × (Y + Z)) (X × Y + X × Z)
distr = uncurry h ∙ swap


--Lema utilizado en la prueba de "distr-undistr".
lema₁ : ∀{X X' Y Z}{f : Hom X (Y ⇒ Z)}{g : Hom (Y × X') Z}{h : Hom X' X}
       → (f ∙ h ≅ curry (g ∙ swap))
       → (uncurry f ∙ swap) ∙ pair iden h ≅ g
lema₁ {f = f} {g} {h} prop = proof
                               (uncurry f ∙ swap) ∙ pair iden h
                               ≅⟨ ass ⟩
                               uncurry f ∙ (swap ∙ pair iden h)
                               ≅⟨ congr swap-pair ⟩
                               uncurry f ∙ (pair h iden ∙ swap)
                               ≅⟨ sym ass ⟩
                               (uncurry f ∙ pair h iden) ∙ swap
                               ≅⟨ congl uncurry-prop₃ ⟩
                               uncurry (f ∙ h) ∙ swap
                               ≅⟨ cong (λ x → uncurry x ∙ swap) prop ⟩
                               uncurry (curry (g ∙ swap)) ∙ swap
                               ≅⟨ congl lawcurry1 ⟩
                               (g ∙ swap) ∙ swap
                               ≅⟨ ass ⟩
                               g ∙ (swap ∙ swap)
                               ≅⟨ congr double-swap ⟩
                               g ∙ iden
                               ≅⟨ idr ⟩
                               g ∎


--Lema utilizado en la prueba de "lema₃".
lema₂ : ∀{X Y Z Z'}{f : Hom (Y × X) Z}{g : Hom Z (Y × Z')}{h : Hom X Z'}
        → g ∙ f ≅ pair iden h
        → map⇒ g ∙ curry (f ∙ swap) ≅ curry swap ∙ h
lema₂ {f = f} {g} {h} prop = proof
                               map⇒ g ∙ curry (f ∙ swap)
                               ≅⟨ curry-prop₃ ⟩
                               curry (g ∙ f ∙ swap)
                               ≅⟨ cong (λ x → curry x) (sym ass) ⟩
                               curry ((g ∙ f) ∙ swap)
                               ≅⟨ cong (λ x → curry (x ∙ swap)) prop ⟩
                               curry (pair iden h ∙ swap)
                               ≅⟨ cong (λ x → curry x) (sym swap-pair) ⟩
                               curry (swap ∙ pair h iden)
                               ≅⟨ sym curry-prop₁ ⟩
                               curry swap ∙ h ∎


--Lema utilizado en la prueba de "undistr-distr".
lema₃ : ∀{X Y Z} → map⇒ (undistr {X} {Y} {Z}) ∙ h ≅ curry swap
lema₃ = proof
          map⇒ undistr ∙ h
          ≅⟨ co-fusion ⟩
          [ map⇒ undistr ∙ curry (inl ∙ swap) ,
            map⇒ undistr ∙ curry (inr ∙ swap) ]
          ≅⟨ cong (λ x → [ x , map⇒ undistr ∙ curry (inr ∙ swap) ]) (lema₂ co-law1) ⟩
          [ curry swap ∙ inl ,
            map⇒ undistr ∙ curry (inr ∙ swap) ]
          ≅⟨ cong (λ x → [ curry swap ∙ inl , x ]) (lema₂ co-law2) ⟩
          [ curry swap ∙ inl , curry swap ∙ inr ]
          ≅⟨ sym co-fusion ⟩
          curry swap ∙ [ inl , inr ]
          ≅⟨ congr copro-iden ⟩
          curry swap ∙ iden
          ≅⟨ idr ⟩
          curry swap ∎


--Forma parte de la prueba de isDist.
distr-undistr : ∀{X Y Z} → distr ∙ undistr ≅ iden {X × Y + X × Z}
distr-undistr = proof
                distr ∙ undistr
                ≅⟨ co-fusion ⟩
                [ (uncurry h ∙ swap) ∙ pair iden inl ,
                  (uncurry h ∙ swap) ∙ pair iden inr ]
                ≅⟨ cong (λ x → [ x , (uncurry h ∙ swap) ∙ pair iden inr ])
                        (lema₁ co-law1) ⟩
                [ inl , (uncurry h ∙ swap) ∙ pair iden inr ]
                ≅⟨ cong (λ x → [ inl , x ]) (lema₁ co-law2) ⟩
                [ inl , inr ]
                ≅⟨ copro-iden ⟩
                iden ∎


--Forma parte de la prueba de isDist.
undistr-distr : ∀{X Y Z} → undistr ∙ distr ≅ iden {X × (Y + Z)}
undistr-distr = proof
                  undistr ∙ uncurry h ∙ swap
                  ≅⟨ sym ass ⟩
                  (undistr ∙ uncurry h) ∙ swap
                  ≅⟨ congl uncurry-prop₂ ⟩
                  uncurry (map⇒ undistr ∙ h) ∙ swap
                  ≅⟨ cong (λ x → uncurry x ∙ swap) lema₃ ⟩
                  uncurry (curry  swap) ∙  swap
                  ≅⟨ congl lawcurry1 ⟩
                  swap ∙ swap
                  ≅⟨ double-swap ⟩
                  iden ∎


--Morfismo "inverso" de "unnull".
inv-unnull : ∀{X} → Hom (X × I) I
inv-unnull = uncurry i ∙ swap


--Forma parte de la prueba de isDist.
prop-null₁ : ∀{X} → unnull ∙ inv-unnull ≅ iden {X × I}
prop-null₁ = proof
               unnull ∙ inv-unnull
               ≅⟨ sym ass ⟩
               (unnull ∙ uncurry i) ∙ swap
               ≅⟨ congl uncurry-prop₂ ⟩
               uncurry (map⇒ i ∙ i) ∙ swap
               ≅⟨ cong (λ x → uncurry x ∙ swap) (sym law) ⟩
               uncurry i ∙ swap
               ≅⟨ cong (λ x → uncurry x ∙ swap) law ⟩
               uncurry (curry swap) ∙ swap
               ≅⟨ congl lawcurry1 ⟩
               swap ∙ swap
               ≅⟨ double-swap ⟩
               iden ∎


--Forma parte de la prueba de isDist.
prop-null₂ : ∀{X} → inv-unnull ∙ unnull {X} ≅ iden {I}
prop-null₂ = proof
             inv-unnull ∙ unnull
             ≅⟨ sym law ⟩
             i
             ≅⟨ law ⟩
             iden ∎


--Probamos que CCC, con coproducto y objeto inicial, es una categoría distributiva.
isDist : Distributive 
isDist = record { distribute = λ {X Y Z} →
                                 iso distr
                                     undistr-distr 
                                     distr-undistr ; 
                  nullify = λ {X} →
                              iso inv-unnull
                                  prop-null₁
                                  prop-null₂ }
