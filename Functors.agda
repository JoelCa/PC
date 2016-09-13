module Functors where

open import Library
open import Categories
open Cat

{- Los Funtores proveen morfismos entre categorías
 Deben preservar la estructura de las mismas.
-}

record Fun (C : Cat)(D : Cat) : Set₁ 
  where
  constructor functor
  field OMap  : Obj C → Obj D
        HMap  : ∀{X Y} → Hom C X Y → Hom D (OMap X) (OMap Y)
        fid   : ∀{X} → HMap (iden C {X}) ≅ iden D {OMap X}
        fcomp : ∀{X Y Z}{f : Hom C Y Z}{g : Hom C X Y} → 
                HMap (_∙_ C f g) ≅ _∙_ D (HMap f) (HMap g)
open Fun

{- ¿Cómo se relaciona con la noción de Functor en Haskell? -}

--------------------------------------------------
{- Ejemplos -}
--------------------------------------------------

{- Funtor Identidad -}
IdF : ∀(C : Cat) → Fun C C
IdF C = functor id id refl refl

--------------------------------------------------
{- Functor Constante
  Mapea todo objeto de C en un objeto de D dado, y todo morfismo a la identidad.
-}

K : ∀{C D : Cat}(X : Cat.Obj D) → Fun C D
K {_} {D} X = functor (λ x → X) (λ x → iden D) refl (sym (proof _∙_ D (iden D) (iden D)
                                                          ≅⟨ idl D ⟩
                                                          iden D ∎))

--------------------------------------------------
{- Funtor Diagonal
  Mapea X al objeto de la categoría producto (X , X)
-}

Δ : ∀{C : Cat} → Fun C (C ×C C)
Δ {C} = functor (λ x → x , x) (λ f → f , f) refl refl

--------------------------------------------------
{- Funtores sobre la categoría Sets -}

{- Funtor cuadrado
  (notar la diferencia con el diagonal para la categoría Sets)
  Mapea X al producto cartesiano X × X
 -}
Cuadrado : Fun Sets Sets
Cuadrado = functor (λ x → x × x) (λ f xy → f (fst xy) , f (snd xy)) refl refl

{- Funtor Producto
  Mapea un objeto de la categoría producto al producto cartesiano.
 -}
Producto : Fun (Sets ×C Sets) Sets
Producto =  functor (λ x → fst x × snd x) (λ f xy → (fst f (fst xy)) , (snd f (snd xy)))
            refl refl

-- Funtor Maybe
open import Data.Maybe.Base renaming (map to mapMaybe)

MaybeF : Fun Sets Sets
MaybeF = functor Maybe
                 mapMaybe
                 {!!}
                 {!!}

-- Funtor Lista 
open import Data.List.Base renaming (map to mapList)

ListF : Fun Sets Sets
ListF = functor List
                mapList
                {!!}
                {!!}

--Bifuntor de árboles con diferente información en nodos y hojas
data Tree (A B : Set) : Set where
     leaf : A → Tree A B
     node : (lt : Tree A B) → B → (rt : Tree A B) → Tree A B

mapTree : ∀{A A' B B'} → (A → A') → (B → B') → Tree A B → Tree A' B'
mapTree = {!!}

TreeF : Fun (Sets ×C Sets) Sets
TreeF = {!!}

--------------------------------------------------
{- Hom functor : probar que el Hom de una categoría C
  es un bifunctor Hom : (C Op) ×C C → Sets
  -}

--------------------------------------------------
{- Composición de funtores -}
_○_ : ∀{C : Cat}{D : Cat}{E : Cat} → 
      Fun D E → Fun C D → Fun C E
_○_ {C}{D}{E} F G = {!!}
    
infixr 10 _○_

--------------------------------------------------
{- ¿Cuándo dos funtores son iguales ?
  Cuando
  1. el mapeo de objetos es igual
  2. Para cualquier par de objetos X,Y, el mapeo de Hom(X,Y) es el mismo

  Notar que las pruebas de las propiedades no son relevantes.
-}
FunctorEq : ∀{C : Cat}{D : Cat}
         →  (F G : Fun C D)
         →  OMap F ≅ OMap G
         →  (λ {X Y} → HMap F {X}{Y}) ≅ (λ {X}{Y} → HMap G {X}{Y})
         → F ≅ G
FunctorEq = {!!}

--------------------------------------------------

{- Categoría (grande) de categorías chicas Dado que tenemos un funtor
  identidad, y que la composición de funtores es un funtor, tenemos
  una categoría CAT, cuyos objetos son categorías, y sus flechas son
  funtores.
-}

{-
CAT : Cat
CAT = record
           { Obj = Cat
           ; Hom = Fun
           ; iden = IdF
           ; _∙_ = _○_
           ; idl = FunctorEq refl refl
           ; idr = FunctorEq refl refl
           ; ass = FunctorEq refl refl
           }
-}


--------------------------------------------------

{- Ejercicio: Probar que los funtores preservan isomorfismos Es decir,
que si tenemos un funtor F : C → D, y f es un componente de un
isomorfismo en C, entonces (HMap F f) es un isomotfismo en D.

-}

open Iso

FunIso : ∀{C D}(F : Fun C D){X Y}{f : Cat.Hom C X Y}
       → Iso {C} X Y f → Iso {D} _ _ (HMap F f)
FunIso  = {!!}

--------------------------------------------------

{- Ejercicio EXTRA: En una clase anterior definimos un Monoide M como
   categoría (MonCat M) con un solo objeto.  Probar que dar funtor F :
   (MonCat M) → (MonCat N) es equivalente a dar un homomorfismo de
   monoides entre M y N.

-}


