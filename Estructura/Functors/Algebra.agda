
open import Categories
open import Functors

module Functors.Algebra {a}{b}{C : Cat {a}{b}}(F : Fun C C) where

open import Library

--------------------------------------------------
-- Suponemos que trabajamos con una categoría C dada y
-- un endofunctor F sobre ella
--------------------------------------------------
open Cat C
open Fun F

--------------------------------------------------
-- Una F-algebra es un objeto X de la categoría base
-- y una función F X → X

record F-algebra : Set (a ⊔ b) where
   constructor falgebra
   field
      carrier : Obj
      algebra : Hom (OMap carrier) carrier 

open F-algebra public


--------------------------------------------------
{- Un homomorfismo de álgebras <A,α> → <B,β> consiste en:
    un morfismo h entre los portadores de las algebras A → B
    una prueba de que se preserva la estructura:

        FA ----HMap F h ----> FB
        |                      |
        α                      β
        |                      |
        V                      V
        a-----------h--------> B
-}

record F-homomorphism (f g : F-algebra): Set (a ⊔ b) where
   constructor homo
   field
      homo-base : Hom (carrier f) (carrier g)
      homo-prop :  homo-base  ∙ algebra f ≅ algebra g ∙ HMap (homo-base) 

open F-homomorphism

--------------------------------------------------
{- Como es usual definimos cuando dos morfismos en la categoría
   son iguales: en este caso serán iguales si sus respectivos morfismos
   de C (homo-base) son iguales.
-}

homomorphismEq : {x y : F-algebra}
              → {h k : (F-homomorphism) x y}
              → homo-base h ≅ homo-base k
              → h ≅ k  
homomorphismEq {h = homo homo-base homo-prop} {homo .homo-base homo-prop₁} refl =
                                cong (homo homo-base) (ir homo-prop homo-prop₁)

--------------------------------------------------
{- La identidad es un homomorfismo -}

iden-homo : {h : F-algebra} → (F-homomorphism) h h
iden-homo {h} = homo (iden) (proof 
                            iden ∙ algebra h
                            ≅⟨ idl ⟩ 
                            algebra h
                            ≅⟨ sym idr ⟩
                            algebra h ∙ iden
                            ≅⟨ cong (λ x → algebra h ∙ x) (sym fid) ⟩
                            algebra h ∙ HMap iden ∎ )

--------------------------------------------------
{- La composición de homomorfismo es un homomorfismo -}
--composition of homomorphisms
comp-homo : {x y z : F-algebra} 
             → (F-homomorphism) y z
             → (F-homomorphism) x y
             → (F-homomorphism) x z
comp-homo {x} {y} {z} (homo g hp₁) (homo f hp₂) =
  homo (g ∙ f) (proof
               (g ∙ f) ∙ algebra x
               ≅⟨ ass ⟩
               g ∙ (f ∙ algebra x)
               ≅⟨ cong (λ w → g ∙ w) hp₂ ⟩
               g ∙ (algebra y ∙ HMap f)
               ≅⟨ sym ass ⟩
               (g ∙ algebra y) ∙ HMap f
               ≅⟨ cong (λ w → w ∙ HMap f) hp₁ ⟩
               (algebra z ∙ HMap g) ∙ HMap f
               ≅⟨ ass ⟩
               algebra z ∙ (HMap g ∙ HMap f)
               ≅⟨ cong (λ w → algebra z ∙ w) (sym fcomp) ⟩
               algebra z ∙ HMap (g ∙ f) ∎)

--------------------------------------------------
{- Con todo lo anterior podemos definir la categoría de
   F-Algebras.
-}

F-AlgebraCat : Cat
F-AlgebraCat = record
                   { Obj  = F-algebra
                   ; Hom  = F-homomorphism
                   ; iden = iden-homo
                   ; _∙_  = comp-homo
                   ; idl  = homomorphismEq idl
                   ; idr  = homomorphismEq idr
                   ; ass  = homomorphismEq ass
                   }
                   
--------------------------------------------------
{- Mapear un algebra <X,h> bajo un functor
   es un algebra <FX, _> -}

mapF : F-algebra → F-algebra
mapF (falgebra x alg) = falgebra (OMap x) (HMap alg)

--------------------------------------------------

open import Categories.Initial

{- Suponemos que la categoría tiene un álgebra inicial
(en general esto depende de F, pero siempre existe para
 los funtores polinomiales)
-}
postulate inF : F-algebra
postulate F-initiality : Initial F-AlgebraCat inF

-- Por comodidad nombramos los componentes del álgebra inicial
open Initial F-initiality renaming (i to init-homo ; law to univ) public
open F-algebra inF renaming (carrier to μF ; algebra to α) public

{- El fold se obtiene (en forma genérica) usando algebras iniciales -}
fold : ∀{X : Obj} → (f : Hom (OMap X) X) → Hom μF X 
fold {X} f = homo-base (init-homo {falgebra X f})

{- El algebra inicial es un homomorfismo -}
α-homo : F-homomorphism (mapF inF) inF
α-homo = homo α refl

--------------------------------------------------
{- Lema de Lambek -}
{- El álgebra inicial es un isomorfismo -}

open import Categories.Iso

lemma : comp-homo α-homo init-homo ≅ iden-homo
lemma = {!!}

L : Iso F-AlgebraCat α-homo
L = {!!}


