
module Categories.Monoids where

 open import Library
 open import Categories

 record Monoid {a} : Set (lsuc a)  where
  infixr 7 _●_
  field  Carrier : Set a
         _●_     : Carrier → Carrier → Carrier  {- ● = \ci -}
         ε       : Carrier
         lid     : {x : Carrier} → ε ● x ≅ x
         rid     : {x : Carrier} → x ● ε ≅ x
         assoc   : {x y z : Carrier} → (x ● y) ● z ≅ x ● (y ● z) 

 open Monoid

 record Monoid-Homo (M N : Monoid) : Set where
   constructor monoid-homo
   open Monoid M renaming (Carrier to cM; ε to ε₁ ;  _●_ to _∙₁_)
   open Monoid N renaming (Carrier to cN; ε to ε₂ ;  _●_ to _∙₂_)
   field
    morph : cM → cN
    preserves-unit : morph ε₁ ≅ ε₂
    preserves-mult : ∀{x y} → morph (x ∙₁ y) ≅ morph x ∙₂ morph y 


 open Monoid-Homo

 idMon : {M : Monoid} → Monoid-Homo M M
 idMon = record { morph = id
                ; preserves-unit = refl
                ; preserves-mult = refl }

 monoid-homo-Eq : {M N : Monoid}{f g : Monoid-Homo M N}
               → morph f ≅ morph g → f ≅ g
 monoid-homo-Eq {f = monoid-homo morph pu pm} {monoid-homo .morph qu qm} refl =
                  cong₂ (monoid-homo morph) (ir pu qu) (i2ir pm qm)

 idComp : { M N O : Monoid} →  Monoid-Homo N O → Monoid-Homo M N → Monoid-Homo M O
 idComp {M} {N} {O} (monoid-homo f pu pm) (monoid-homo g qu qm) =
                         (record { morph = f ∘ g
                                 ; preserves-unit = 
                                       proof
                                       f (g (ε M))
                                       ≅⟨ cong f qu ⟩
                                       f (ε N)
                                       ≅⟨ pu ⟩
                                       ε O
                                       ∎
                                 ; preserves-mult = λ {x} {y} →
                                       proof
                                       f (g (Monoid._●_ M x y))
                                       ≅⟨ cong f qm ⟩
                                       f (Monoid._●_ N (g x) (g y))
                                       ≅⟨ pm ⟩
                                       Monoid._●_ O (f (g x)) (f (g y))
                                       ∎ })


 MonCat : Cat
 MonCat = let open Monoid in
         record
           { Obj = Monoid
           ; Hom = Monoid-Homo
           ; iden = idMon
           ; _∙_ = idComp
           ; idl = monoid-homo-Eq refl
           ; idr = monoid-homo-Eq refl
           ; ass = monoid-homo-Eq refl
           }

