module Adjunctions where

open import Library
open import Categories
open import Functors

open Fun

record Adj {a b c d}(C : Cat {a}{b})(D : Cat {c}{d}) : Set (a ⊔ b ⊔ c ⊔ d)
  where
  constructor adjunction  
  open Cat C renaming (Obj to ObjC ; Hom to HomC ; _∙_ to _∙C_ )
  open Cat D renaming (Obj to ObjD ; Hom to HomD ; _∙_ to _∙D_ )
  field L        : Fun C D
        R        : Fun D C
        left     : {X : ObjC}{Y : ObjD} → 
                   HomD (OMap L X) Y → HomC X (OMap R Y)
        right    : {X : ObjC}{Y : ObjD} → 
                   HomC X (OMap R Y) → HomD (OMap L X) Y
        lawa     : {X : ObjC}{Y : ObjD}(f : HomD (OMap L X) Y) → 
                   right (left f) ≅ f
        lawb     : {X : ObjC}{Y : ObjD}(f : HomC X (OMap R Y)) →
                   left (right f) ≅ f
        natleft  : {X X' : ObjC}{Y Y' : ObjD}
                   (f : HomC X' X)(g : HomD Y Y')
                   (h : HomD (OMap L X) Y) → 
                   HMap R g ∙C left h ∙C f  ≅ left (g ∙D h ∙D HMap L f) 
        natright : {X X' : ObjC}{Y Y' : ObjD}
                   (f : HomC X' X)(g : HomD Y Y')
                   (h : HomC X (OMap R Y)) → 
                   right (HMap R g ∙C h ∙C f) ≅  g ∙D (right h ∙D HMap L f) 
