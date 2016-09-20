module Categories where

open import Library

--------------------------------------------------
record Cat {a b} : Set (lsuc (a ⊔ b)) where
  infixr 7 _∙_
  field Obj  : Set a
        Hom  : Obj → Obj → Set b
        iden : ∀{X} → Hom X X
        _∙_ : ∀{X Y Z} → Hom Y Z → Hom X Y → Hom X Z
        idl  : ∀{X Y}{f : Hom X Y} → iden ∙ f ≅ f
        idr  : ∀{X Y}{f : Hom X Y} → f ∙ iden ≅ f
        ass  : ∀{W X Y Z}{f : Hom Y Z}{g : Hom X Y}{h : Hom W X} → 
               (f ∙ g) ∙ h ≅  f ∙ (g ∙ h)
               
open Cat

--------------------------------------------------
_Op : ∀{a b} → Cat {a} {b} → Cat
C Op = 
  record{
  Obj  = Obj C; 
  Hom  = λ X Y → Hom C Y X;
  iden = iden C;
  _∙_ = λ f g → _∙_ C g f; 
  idl  = idr C;
  idr  = idl C;
  ass  = sym (ass C)}
