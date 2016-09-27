module Categories.Slice where

open import Library
open import Categories

--------------------------------------------------
{- Categorías Slice -}

{- Dada una categoría C, los objetos de un slice sobre un objeto I, son morfismos con codominio I
-}

record Slice₀ {a b}(C : Cat {a} {b})(I : Cat.Obj C) : Set (a ⊔ b) where
  constructor _,_
  open Cat C
  field
     base : Obj
     morObj : Hom base I

open Slice₀

{- record para representar los morfismos de la categoría -}
record Slice₁ {a b}(C : Cat {a} {b})(I : Cat.Obj C)(X Y : Slice₀ C I) : Set b
  where
  constructor _,_
  open Cat C
  field
    baseHom : Hom (base X) (base Y)
    prop :  morObj Y ∙ baseHom ≅ morObj X
      
     {- para probar que dos morfismos de slice son iguales
     no nos interesa cual es la prueba de pro.
     Cualquier prueba es suficiente
      -}

open Slice₁

{- igualdad de morfismos en esta categoría.
   notar como usamos proof-irrelevance.
-}
Slice₁-eq : ∀{a b}{C : Cat {a} {b}}{I : Cat.Obj C}{X Y : Slice₀ C I}
          → {f g : Slice₁ C I X Y}
          → baseHom f ≅ baseHom g
          → f ≅ g
Slice₁-eq {f = baseHom , prop} {.baseHom , prop₁} refl =
         cong (_,_ baseHom) (pir prop prop₁)

{- la composición es simplemente pegar triángulos -}
Slice-comp : ∀{a b}{C : Cat {a} {b}}{I : Cat.Obj C}
             → {X Y Z :  Slice₀ C I}
             → Slice₁ C I Y Z --Hom Y Z
             → Slice₁ C I X Y --Hom X Y
             → Slice₁ C I X Z --Hom X Z
Slice-comp {C = C}{X = X , x} {Y , y} {Z , z} (f , p) (g , q) =
      let open Cat C in
          f ∙ g , (
            proof
            z ∙ (f ∙ g)
           ≅⟨ sym ass ⟩
             (z ∙ f) ∙ g
           ≅⟨ cong (λ h → h ∙ g) p ⟩
             y ∙ g
           ≅⟨ q ⟩
             x
            ∎)

Slice : ∀{a b}(C : Cat {a} {b})(I : Cat.Obj C) → Cat
Slice C I = let open Cat C in
           record
              { Obj = Slice₀ C I
              ; Hom = Slice₁ C I
              ; iden = iden  , idr 
              ; _∙_ = Slice-comp
              ; idl = Slice₁-eq idl
              ; idr = Slice₁-eq idr
              ; ass = Slice₁-eq ass
              }
