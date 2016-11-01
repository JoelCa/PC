module Categories.Iso where

open import Library
open import Categories


--------------------------------------------------
{- Isomorfismo en una categoría -}

record Iso {a b}(C : Cat {a} {b}){A B}(f : Cat.Hom C A B) : Set b
  where
  constructor iso
  open Cat C
  field inv  : Hom B A
        rinv : f ∙ inv ≅ iden {B}
        linv : inv ∙ f ≅ iden {A}

open Iso

--------------------------------------------------
{- La identidad es un isomorfismo -}

id-iso : ∀{a b}(C : Cat {a} {b}){X} → Iso C (Cat.iden C {X})
id-iso C = iso (Cat.iden C) (Cat.idl C) (Cat.idr C)

--------------------------------------------------
{- Los isomorfismos son cerrados bajo composición -}

comp-iso : ∀{a b}(C : Cat {a} {b}){X Y Z}{f : Cat.Hom C Y Z}{g : Cat.Hom C X Y} →
            Iso C f → Iso C g → Iso C (Cat._∙_ C f g)
comp-iso C {f = f} {g} (iso inv law1 law2) (iso inv₁ law3 law4)
            = let open Cat C in 
            iso (inv₁ ∙ inv)
                (proof
                  (f ∙ g) ∙ (inv₁ ∙ inv)
                  ≅⟨ trans ass (cong (_∙_ f) (sym ass)) ⟩
                   f ∙ (g ∙ inv₁) ∙ inv
                  ≅⟨ trans (cong (λ x → f ∙ x ∙ inv) law3) (cong (_∙_ f) idl) ⟩
                  f ∙ inv
                  ≅⟨ law1 ⟩
                  iden
                ∎)
                (proof
                  (inv₁ ∙ inv) ∙ f ∙ g
                  ≅⟨ trans ass (cong (_∙_ inv₁) (sym ass)) ⟩
                  inv₁ ∙ (inv ∙ f) ∙ g
                  ≅⟨ cong (λ x → _∙_ inv₁ (_∙_ x g)) law2 ⟩
                  inv₁ ∙ iden ∙ g
                  ≅⟨ cong (_∙_ inv₁) idl ⟩
                  inv₁ ∙ g
                  ≅⟨ law4 ⟩
                  iden
                ∎)

--------------------------------------------------
{-  Un componente de un isomorfismo
   sólo puede pertenecer a un único isomorfismo -}

iso-ir-aux :  ∀{a b}(C : Cat {a} {b}){A B}{f : Cat.Hom C A B} →
         (p q : Iso C f) → inv p ≅ inv q → p ≅ q
iso-ir-aux C (iso inv law1 law2) (iso .inv law3 law4) refl =
                cong₂ (iso inv) (ir law1 law3) (ir law2 law4)
 
isoEq :  ∀{a b}(C : Cat {a} {b}){A B}{f : Cat.Hom C A B} →
         (p q : Iso C f) → p ≅ q
isoEq C {f = f} p q = let open Cat C in
            iso-ir-aux C p q (
                   proof
                   inv p
                   ≅⟨ sym idr ⟩
                   inv p ∙ iden
                   ≅⟨ cong (_∙_ (inv p)) (sym (rinv q)) ⟩
                   inv p ∙ (f ∙ inv q)
                   ≅⟨ sym ass ⟩
                   (inv p ∙ f) ∙ inv q
                   ≅⟨ cong (λ x → x ∙ (inv q)) (linv p) ⟩
                   iden ∙ inv q
                   ≅⟨ idl ⟩                   
                   inv q
                   ∎) 

--------------------------------------------------
{- Un isormofismo en (C : Cat) es un isomorfismo en (C Op). -}

iso-op : ∀{a b}{C : Cat {a} {b}}{A B}{f : Cat.Hom C A B} →  Iso (C Op) f → Iso C f
iso-op (iso inv law1 law2) = iso inv law2 law1

iso-op' : ∀{a b}{C : Cat {a} {b}}{A B}{f : Cat.Hom C A B} →  Iso C f → Iso (C Op) f
iso-op' (iso inv law1 law2) = iso inv law2 law1
