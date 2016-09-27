
module Categories.Cat where

open import Library
open import Categories
open import Functors

{- Categoría (grande) de categorías chicas
-}

CAT : ∀{a}{b} → Cat
CAT {a}{b} = record
           { Obj = Cat {a} {b}
           ; Hom = Fun
           ; iden = IdF
           ; _∙_ = _○_
           ; idl = Functor-Eq refl refl
           ; idr = Functor-Eq refl refl
           ; ass = Functor-Eq refl refl
           }
