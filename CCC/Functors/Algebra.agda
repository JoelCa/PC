
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

open F-algebra


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
iden-homo {h} = record {
                   homo-base = iden;
                   homo-prop = proof
                    iden ∙ algebra h
                    ≅⟨ idl ⟩
                    algebra h
                    ≅⟨ sym idr ⟩
                    algebra h ∙ iden
                    ≅⟨ congr (sym fid) ⟩
                    algebra h ∙ HMap iden
                    ∎
 }

--------------------------------------------------
{- La composición de homomorfismo es un homomorfismo -}
--composition of homomorphisms
comp-homo : {x y z : F-algebra} 
             → (F-homomorphism) y z
             → (F-homomorphism) x y
             → (F-homomorphism) x z
comp-homo {x}{y}{z} h k =
                 record {
                   homo-base = homo-base h ∙ homo-base k ;
                   homo-prop = proof
                    (homo-base h ∙ homo-base k) ∙ algebra x
                    ≅⟨ ass ⟩
                    homo-base h ∙ (homo-base k ∙ algebra x)
                    ≅⟨ congr (homo-prop k) ⟩
                    homo-base h ∙ (algebra y ∙ HMap (homo-base k))
                    ≅⟨ sym ass ⟩
                    (homo-base h ∙ algebra y) ∙ HMap (homo-base k)
                    ≅⟨ congl (homo-prop h) ⟩
                    (algebra z ∙ HMap (homo-base h)) ∙ HMap (homo-base k)
                    ≅⟨ ass ⟩
                    algebra z ∙ (HMap (homo-base h) ∙ HMap (homo-base k))
                    ≅⟨ congr (sym fcomp) ⟩                    
                     algebra z ∙ HMap (homo-base h ∙ homo-base k)
                  ∎ } 

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
{- Mapear un algebra <X,h> bajo un funtor
   es un algebra <FX, _> -}

mapF : F-algebra → F-algebra
mapF (falgebra carrier algebra) = falgebra (OMap carrier) (HMap algebra)

--------------------------------------------------
{- Tenemos un funtor que se olvida de la estructura y
   nos devuelve sólo el portador de las algebras y el morfismo base
-}
   
ForgetfulAlgebra : Fun (F-AlgebraCat) C
ForgetfulAlgebra = record{ OMap = carrier
                      ; HMap = homo-base
                      ; fid = refl
                      ; fcomp = refl}


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
lemma = homomorphismEq (proof
           α ∙ homo-base init-homo
         ≅⟨ sym (cong homo-base (univ {f = comp-homo α-homo init-homo}) ) ⟩
           homo-base init-homo
         ≅⟨ cong homo-base (univ {f = iden-homo}) ⟩
          iden
         ∎)

L : Iso F-AlgebraCat α-homo
L = iso init-homo
        lemma
        (homomorphismEq (proof
           homo-base init-homo ∙ α
           ≅⟨ homo-prop init-homo  ⟩
           HMap α ∙ HMap (homo-base init-homo)
           ≅⟨ sym fcomp ⟩
           HMap (α ∙ homo-base init-homo)
           ≅⟨ cong HMap (cong homo-base lemma) ⟩
           HMap iden
           ≅⟨ fid ⟩
           iden
           ∎ ))


