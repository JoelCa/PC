
open import Categories
open import Categories.Products


module Categories.Products.Properties {l m}{C : Cat {l}{m}}(p : Products C) where

open import Library hiding (_×_ ; swap)
open Cat C
open Products p
open ProductMorphisms p using (swap)


--MODIFICADO
π₁-pair : ∀{A B C D}{f : Hom A C}{g : Hom B D} → π₁ ∙ pair f g ≅ f ∙ π₁ {A} {B}
π₁-pair = law1

--MODIFICADO
π₂-pair : ∀{A B C D}{f : Hom A C}{g : Hom B D} → π₂ ∙ pair f g  ≅ g ∙ π₂ {A} {B}
π₂-pair = law2


iden-pair : ∀{A B} →  pair (iden {A}) (iden {B}) ≅ iden {A × B}
iden-pair = sym (law3 (trans idr (sym idl)) (trans idr (sym idl)))

pro-iden : ∀{A B} → ⟨ π₁{A} {B} , π₂ ⟩ ≅ iden
pro-iden = sym (law3 idr idr)

fusion : ∀{A B C D}{f : Hom C A}{g : Hom C B}{h : Hom D C}
        → ⟨ f , g ⟩ ∙ h ≅  ⟨ f ∙  h , g ∙ h ⟩
fusion {f = f}{g}{h} = law3 (trans (sym ass) (congl law1)) (trans (sym ass) (congl law2))

fusion-pair : ∀{A B C D E}{f : Hom B A}{g : Hom D C}{h : Hom E B}{i : Hom E D} 
          → pair f g ∙ ⟨ h , i ⟩ ≅ ⟨ f ∙ h , g ∙ i ⟩
fusion-pair {f = f}{g}{h}{i}= law3 (proof
                   π₁ ∙ ⟨ f ∙ π₁ , g ∙ π₂ ⟩ ∙ ⟨ h , i ⟩
                ≅⟨ congr fusion ⟩
                   π₁ ∙ ⟨ (f ∙ π₁) ∙ ⟨ h , i ⟩ , (g ∙ π₂) ∙ ⟨ h , i ⟩ ⟩
                ≅⟨ law1 ⟩
                   (f ∙ π₁) ∙ ⟨ h , i ⟩
                ≅⟨ ass ⟩
                  f ∙ π₁ ∙ ⟨ h , i ⟩
                ≅⟨ congr law1 ⟩
                  f ∙ h
                ∎)
                  (proof
                  π₂ ∙ ⟨ f ∙ π₁ , g ∙ π₂ ⟩ ∙ ⟨ h , i ⟩
                  ≅⟨ congr fusion ⟩
                  π₂ ∙ ⟨ (f ∙ π₁) ∙ ⟨ h , i ⟩ , (g ∙ π₂) ∙ ⟨ h , i ⟩ ⟩
                  ≅⟨ law2 ⟩
                  (g ∙ π₂) ∙ ⟨ h , i ⟩
                  ≅⟨ ass ⟩
                  g ∙ π₂ ∙ ⟨ h , i ⟩
                  ≅⟨ congr law2 ⟩
                  g ∙ i
                ∎)


swap-pair : ∀{A B C D}{f : Hom A B}{g : Hom C D} →
            swap ∙ pair f g ≅ pair g f ∙ swap
swap-pair {f = f} {g}= proof swap ∙ pair f g
                       ≅⟨ fusion ⟩
                       ⟨ π₂ ∙ pair f g , π₁ ∙ pair f g ⟩
                       ≅⟨ cong₂ (λ x y → ⟨ x , y ⟩) π₂-pair π₁-pair ⟩
                       ⟨ g ∙ π₂ , f ∙ π₁ ⟩
                       ≅⟨ cong₂ (λ x y →  ⟨ g ∙ x , f ∙ y ⟩) (sym law1) (sym law2) ⟩
                       ⟨ g ∙ (π₁ ∙ ⟨ π₂ , π₁ ⟩) , f ∙ (π₂ ∙ ⟨ π₂ , π₁ ⟩) ⟩
                       ≅⟨ cong₂ (λ x y → ⟨ x , y ⟩) (sym ass) (sym ass) ⟩
                       ⟨ (g ∙ π₁) ∙ ⟨ π₂ , π₁ ⟩ , (f ∙ π₂) ∙ ⟨ π₂ , π₁ ⟩ ⟩
                       ≅⟨ sym fusion ⟩
                       pair g f ∙ swap ∎

double-swap : ∀{A B} → swap ∙ swap {A} {B} ≅ iden
double-swap = proof
              swap ∙ swap
              ≅⟨ fusion ⟩
              ⟨ π₂ ∙ swap , π₁ ∙ swap ⟩
              ≅⟨ cong₂ (λ x y → ⟨ x , y ⟩) law2 law1 ⟩
              ⟨ π₁ , π₂ ⟩
              ≅⟨ pro-iden ⟩
              iden ∎


comp-pair :  ∀{A B C A' B' C'}{f : Hom B C}{g : Hom A B}{h : Hom B' C'}{i : Hom A' B'}
          → pair (f ∙ g) (h ∙ i) ≅  pair f h ∙ pair g i
comp-pair {f = f}{g}{h}{i} = proof
                 ⟨ (f ∙ g) ∙ π₁ , (h ∙ i) ∙ π₂ ⟩
              ≅⟨ cong₂ ⟨_,_⟩ ass ass ⟩
                 ⟨ f ∙ g ∙ π₁ , h ∙ i ∙ π₂ ⟩
              ≅⟨ sym fusion-pair ⟩
                 pair f h ∙ pair g i
               ∎

iden-comp-pair :  ∀{A B C D}{f : Hom B C}{g : Hom A B}
                  → pair (f ∙ g) (iden {D}) ≅ pair f iden ∙ pair g iden
iden-comp-pair {f = f} {g} = proof
                             pair (f ∙ g) iden
                             ≅⟨ cong (λ x → pair (f ∙ g) x) (sym idl) ⟩
                             pair (f ∙ g) (iden ∙ iden)
                             ≅⟨ comp-pair ⟩
                             pair f iden ∙ pair g iden ∎

