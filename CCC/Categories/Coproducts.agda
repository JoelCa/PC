module Categories.Coproducts where

open import Data.Sum hiding ([_,_])
open import Library hiding (_+_ ; _,_)
open import Categories

record Coproducts {l m}(C : Cat {l}{m}) : Set (m ⊔ l) where
  constructor coproduct
  open Cat C
  infixr 2 _+_
  field _+_   : Obj → Obj → Obj
        inl   : ∀{A B} → Hom A (A + B)
        inr   : ∀{A B} → Hom B (A + B)
        [_,_] : ∀{A B C} -> Hom A C -> Hom B C -> Hom (A + B) C
        law1  : ∀{A B C}{f : Hom A C}{g : Hom B C} →
                [ f , g ] ∙ inl ≅ f
        law2  : ∀{A B C}{f : Hom A C}{g : Hom B C} →
                [ f , g ] ∙ inr ≅ g
        law3  : ∀{A B C}{f : Hom A C}{g : Hom B C}{h : Hom (A + B) C} →
                h ∙ inl ≅ f → h ∙ inr ≅ g → h ≅ [ f , g ]
                
  copair : ∀{X Y Z W}(f : Hom X Z)(g : Hom Y W) → Hom (X + Y) (Z + W)
  copair f g = [ inl ∙ f , inr ∙ g ]

open import Categories.Products

--------------------------------------------------------
-- Los coproductos son productos en la categoría dual (y viceversa)
ProductCoproductDuality : ∀{a}{b}{C : Cat {a}{b}}
                        → Products C
                        → Coproducts (C Op)
ProductCoproductDuality (prod _×_ π₁ π₂ ⟨_,_⟩ law1 law2 law3) = coproduct _×_ π₁ π₂ ⟨_,_⟩ law1 law2 law3

CoproductProductDuality : ∀{a}{b}{C : Cat {a}{b}}
                        → Coproducts C
                        → Products (C Op)
CoproductProductDuality (coproduct _+_ inl inr [_,_] law1 law2 law3) = prod _+_ inl inr [_,_] law1 law2 law3

--------------------------------------------------
module CoproductIso {a}{b}(C : Cat {a}{b})  where

  open import Categories.Iso
  open Coproducts
  open Iso

  open Cat C

  open import Categories.Products

  open ProductIso (C Op) renaming (ProductIso to piso)

  {- Los coproductos son únicos hasta un isomorfismo (usando dualidad) -}
  CoproductIso : ∀{A B}(X Y : Coproducts C) → Iso C ([_,_] X {A} {B} (inl Y) (inr Y))
  CoproductIso X Y = iso-op (piso (CoproductProductDuality X) (CoproductProductDuality Y))

--------------------------------------------------

