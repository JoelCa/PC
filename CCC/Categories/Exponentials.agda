open import Library hiding (_×_)
open import Categories
open import Categories.Products

module Categories.Exponentials {a}{b}{C : Cat {a}{b}}
                               (hasProducts : Products C)                               
                               where


record Exponentials{l}{m}(C : Cat {l}{m})(hasProducts : Products C) : Set (l ⊔ m)
  where
  constructor expo
  open Cat C
  open Products hasProducts
  infixr 5 _^_
  field _^_ : Obj → Obj → Obj
        ε : ∀{B C} → Hom (C ^ B × B) C
        curry[_] : ∀{A B C} → (f : Hom (A × B) C) → Hom A (C ^ B)
        elaw1 : ∀{A B C}{f : Hom (A × B) C} → ε ∙ (pair curry[ f ] iden ) ≅ f
        elaw2 : ∀{A B C}{f : Hom (A × B) C}{h : Hom C (B ^ A)} →
               ε ∙ (pair h iden ) ≅ f → h ≅ curry[ f ]



        
