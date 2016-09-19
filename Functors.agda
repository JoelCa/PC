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

maybeId : ∀ {a} {A : Set a} → (m : Maybe A) → mapMaybe id m ≅  id m
maybeId (just x) = refl
maybeId nothing = refl

maybeComp : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} {f : A → B} {g : B → C} →
  (m : Maybe A) →   mapMaybe (g ∘ f) m ≅ ((mapMaybe g) ∘ (mapMaybe f)) m
maybeComp (just x) = refl
maybeComp nothing = refl


MaybeF : Fun Sets Sets
MaybeF = functor Maybe
                 mapMaybe
                 (ext (λ m → maybeId m))
                 (ext (λ m → maybeComp m))

-- Funtor Lista 
open import Data.List.Base renaming (map to mapList)

listId : ∀ {a} {A : Set a} → (xs : List A) → mapList (id) xs ≅ id xs
listId [] = refl
listId (x ∷ xs) = proof id x ∷ mapList id xs
                  ≅⟨ cong (λ x₁ → id x ∷ x₁) (listId xs) ⟩
                  id x ∷ xs
                  ≅⟨ refl ⟩
                  id (x ∷ xs) ∎

listComp : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} {f : A → B} {g : B → C} →
  (xs : List A) →   mapList (g ∘ f) xs ≅ ((mapList g) ∘ (mapList f)) xs
listComp [] = refl
listComp {f = f} {g} (x ∷ xs) = proof (g ∘ f) x ∷ mapList (g ∘ f) xs
                                ≅⟨ cong (λ x₁ → (g ∘ f) x ∷ x₁) (listComp xs) ⟩
                                (g ∘ f) x ∷ (mapList g ∘ mapList f) xs
                                ≅⟨ refl ⟩
                                (mapList g ∘ mapList f) (x ∷ xs) ∎


ListF : Fun Sets Sets
ListF = functor List
                mapList
                (ext (λ xs → listId xs))
                (ext (λ xs → listComp xs))

--Bifuntor de árboles con diferente información en nodos y hojas
data Tree (A B : Set) : Set where
     leaf : A → Tree A B
     node : (lt : Tree A B) → B → (rt : Tree A B) → Tree A B

mapTree : ∀{A A' B B'} → (A → A') → (B → B') → Tree A B → Tree A' B'
mapTree fl fn (leaf x) = leaf (fl x)
mapTree fl fn (node t₁ x t₂) = node (mapTree fl fn t₁) (fn x) (mapTree fl fn t₂)

treeId :  {A B : Set} → (t : Tree A B) → mapTree (iden Sets)  (iden Sets) t ≅ (iden Sets) t
treeId (leaf x) = refl
treeId (node t x t₁) = proof
                       node (mapTree (iden Sets) (iden Sets) t) (iden Sets x)
                         (mapTree (iden Sets) (iden Sets) t₁)
                       ≅⟨ refl ⟩
                       node (mapTree (iden Sets) (iden Sets) t) x
                         (mapTree (iden Sets) (iden Sets) t₁)
                       ≅⟨ cong₂ (λ x₁ x₂ → node x₁ x x₂) (treeId t) (treeId t₁) ⟩
                       node t x t₁ ∎

treeComp : {A B C A' B' C' : Set} {f₁ : A → B} {g₁ : B → C} {f₂ : A' → B'} {g₂ : B' → C'} →
  (t : Tree A A') → mapTree (g₁ ∘ f₁) (g₂ ∘ f₂) t ≅  ((mapTree g₁ g₂) ∘ (mapTree f₁ f₂)) t
treeComp (leaf x) = refl
treeComp {f₁ = f₁} {g₁} {f₂} {g₂} (node t x t₁) =
  proof
  node (mapTree (g₁ ∘ f₁) (g₂ ∘ f₂) t) ((g₂ ∘ f₂) x) (mapTree (g₁ ∘ f₁) (g₂ ∘ f₂) t₁)
  ≅⟨ cong₂ (λ x₁ x₂ → node x₁ ((g₂ ∘ f₂) x) x₂) (treeComp t) (treeComp t₁) ⟩
  node ((mapTree g₁ g₂ ∘ mapTree f₁ f₂) t) ((g₂ ∘ f₂) x)
    ((mapTree g₁ g₂ ∘ mapTree f₁ f₂) t₁)
  ≅⟨ refl ⟩
  (mapTree g₁ g₂ ∘ mapTree f₁ f₂) (node t x t₁)
  ∎


TreeF : Fun (Sets ×C Sets) Sets
TreeF = functor (λ x → Tree (fst x) (snd x)) (λ fg t → mapTree (fst fg) (snd fg) t)
  (ext (λ t → treeId t)) (ext (λ t → treeComp t))

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


