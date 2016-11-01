module Categories.Two where

open import Categories
open import Library

--------------------------------------------------

{- Categoría con dos objetos y un morfismo entre ellos (además de las
   identidades) -}

open Cat
open import Data.Bool

Two : Cat
Two = record
        { Obj = Bool
        ; Hom = λ _ _ → ⊤
        ; iden = ⊤.tt
        ; _∙_ = λ _ _ → ⊤.tt
        ; idl = refl
        ; idr = refl
        ; ass = refl
        }
