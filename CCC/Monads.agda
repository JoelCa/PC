module Monads where

open import Library
open import Categories

{- Mónadas à la Haskell (Tripletas de Kleisli) -}

record Monad {a}{b}(C : Cat {a}{b}) : Set (a ⊔ b) where
  constructor monad
  open Cat C
  field T      : Obj → Obj
        return : ∀ {X} → Hom X (T X)
        bind   : ∀{X Y} → Hom X (T Y) → Hom (T X) (T Y)
        mlaw1  : ∀{X} → bind (return {X}) ≅ iden {T X}
        mlaw2  : ∀{X Y}{f : Hom X (T Y)} → bind f ∙ return ≅ f
        mlaw3  : ∀{X Y Z}{f : Hom X (T Y)}{g : Hom Y (T Z)} → 
                  bind (bind g ∙ f)  ≅ bind g ∙ bind f
