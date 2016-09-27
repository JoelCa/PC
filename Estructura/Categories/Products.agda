module Categories.Products where

open import Library hiding (_×_ ; swap)
open import Categories


record Products {l}{m}(C : Cat {l}{m}) : Set (l ⊔ m)
  where
  constructor prod
  open Cat C
  field _×_ : Obj → Obj → Obj
        π₁ : ∀{A B} → Hom (A × B) A
        π₂ : ∀{A B} → Hom (A × B) B
        ⟨_,_⟩ : ∀{A B C} →(f : Hom C A) → (g : Hom C B) → Hom C (A × B)
        law1 : ∀{A B C}{f : Hom C A}{g} → π₁ {A} {B} ∙ ⟨ f , g ⟩ ≅ f
        law2 : ∀{A B C}{f : Hom C A}{g} → π₂ {A} {B} ∙ ⟨ f , g ⟩ ≅ g
        law3 : ∀{A B C}{f : Hom C A}{g : Hom C B}{h : Hom C (A × B)} →
               π₁ ∙ h ≅ f → π₂ ∙ h ≅ g → h ≅ ⟨ f , g ⟩


