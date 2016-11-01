module Functors where

open import Library
open import Categories
open Cat

record Fun {a b c d}(C : Cat {a} {b})(D : Cat {c} {d}) : Set (a ⊔ b ⊔ c ⊔ d) 
  where
  constructor functor
  field OMap  : Obj C → Obj D
        HMap  : ∀{X Y} → Hom C X Y → Hom D (OMap X) (OMap Y)
        fid   : ∀{X} → HMap (iden C {X}) ≅ iden D {OMap X}
        fcomp : ∀{X Y Z}{f : Hom C Y Z}{g : Hom C X Y} → 
                HMap (_∙_ C f g) ≅ _∙_ D (HMap f) (HMap g)

open Fun

--------------------------------------------------
{- Funtor Identidad -}
IdF : ∀{a b}{C : Cat {a} {b}} → Fun C C
IdF {C} = record{ OMap = id
                ; HMap = id
                ; fid = refl
                ; fcomp = refl}


--------------------------------------------------
{- Composición de funtores -}
_○_ : ∀{a b c d e f}{C : Cat {a} {b}}{D : Cat {c} {d}}{E : Cat {e} {f}} → 
      Fun D E → Fun C D → Fun C E
_○_ {C = C}{D}{E} F G = record{
  OMap  = OMap F ∘ OMap G;
  HMap   = HMap F ∘ HMap G;
  fid    = 
    proof
    HMap F (HMap G (iden C)) 
    ≅⟨ cong (HMap F) (fid G) ⟩
    HMap F (iden D)
    ≅⟨ fid F ⟩ 
    iden E 
    ∎;
  fcomp  = λ {_}{_}{_}{f}{g} → 
    proof
    HMap F (HMap G (_∙_ C f g)) 
    ≅⟨ cong (HMap F) (fcomp G)  ⟩ 
    HMap F (_∙_ D (HMap G f) (HMap G g))
    ≅⟨ fcomp F ⟩ 
    _∙_ E (HMap F (HMap G f)) (HMap F (HMap G g)) 
    ∎}
    
infix 10 _○_

--------------------------------------------------
{- ¿Cuándo dos funtores son iguales ?
  Cuando
  1. el mapeo de objetos es igual
  2. Para cualquier par de objetos X,Y, el mapeo de Hom(X,Y) es el mismo

  Notar que las pruebas de las propiedades no son relevantes.
-}
Functor-Eq : ∀{a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}{F G : Fun C D}
         →  OMap F ≅ OMap G
         →  (λ {X Y} → HMap F {X}{Y}) ≅ (λ {X}{Y} → HMap G {X}{Y})
         → F ≅ G
Functor-Eq {F = functor fo fh _ _} {functor .fo .fh _ _} refl refl =
  cong₂ (functor fo fh)
        (iir _ _)
        (iext λ _ → iext λ _ → iext λ _ → iext λ _ → iext λ _ → ir _ _)


--------------------------------------------------

Fop : ∀{a b c d}{C : Cat {a}{b}}{ D : Cat {c} {d}}
      → (F : Fun C D)
      → Fun (C Op) (D Op)
Fop (functor OMap HMap fid fcomp) = functor OMap HMap fid fcomp
