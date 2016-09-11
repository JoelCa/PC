module Categories where

{- importamos definición de igualdad heterogénea (y otras cosas) -}
open import Library

--------------------------------------------------
{- Definición de Categoría -}
{-
 - Una colección de objetos
 - Conjuntos de flechas entre objetos
 - todo objeto tiene una flecha identidad
 - todo par de flechas "compatibles" puede componerse
 - la composición es asociativa, con la flecha identidad como unidad.
-}

record Cat : Set₂ where
  infix 10 _∙_
  field Obj  : Set₁
        Hom  : Obj → Obj → Set
        iden : ∀{X} → Hom X X
        _∙_ : ∀{X Y Z} → Hom Y Z → Hom X Y → Hom X Z
        idl  : ∀{X Y}{f : Hom X Y} → iden ∙ f ≅ f
        idr  : ∀{X Y}{f : Hom X Y} → f ∙ iden ≅ f
        ass  : ∀{W X Y Z}{f : Hom Y Z}{g : Hom X Y}{h : Hom W X} → 
               (f ∙ g) ∙ h ≅  f ∙ (g ∙ h)
               

--------------------------------------------------
{- El típico ejemplo de categoría es la categoría Set de conjuntos y
   funciones entre los mismos.
-}

Sets : Cat
Sets = record
         { Obj = Set
         ; Hom = λ X Y → X → Y
         ; iden = id
         ; _∙_ = λ f g → f ∘ g
         ; idl = refl
         ; idr = refl
         ; ass = refl
         }


--------------------------------------------------
{- Para cada categoría existe la categoría dual, que consiste de los
mismos objetos, pero con las flechas invertidas. -}

_Op : Cat → Cat
C Op = let open Cat C in
       record
         { Obj = Obj
         ; Hom = λ X Y → Hom Y X
         ; iden = iden
         ; _∙_ = λ f g → g ∙ f
         ; idl = idr
         ; idr = idl
         ; ass = sym ass
         }

--------------------------------------------------
--NO lo hacemos
-- {- Categoría Discreta

--    Una categoría discreta es una categoría en la que los únicos
-- morfismos son identidades. La composición y ecuaciones de coherencia
-- son triviales.
-- -}

-- Discrete :  Set → Cat
-- Discrete X = record
--                { Obj = Lift X
--                ; Hom = λ X Y → {!X ≅ Y!}
--                ; iden = {!!}
--                ; _∙_ = {!!}
--                ; idl = {!!}
--                ; idr = {!!}
--                ; ass = {!!}
--                }


-- {- A menudo nos queremos "olvidar" de los morfismos de una
-- categoría. Es decir, miramos a la categoría como una categoría
-- discreta. Esto se nota en lenguaje categórico como |C| -}

-- ∣_∣ : Cat → Cat
-- ∣ C ∣ = {!!}

--------------------------------------------------
{- Categoría Producto -}
{- Dadas dos categorías, podemos formar la categoría producto 
   Los objetos son el producto cartesiano de los objetos
   Los morfismos son pares de flechas.
-}

_×C_ : Cat → Cat → Cat
C ×C D = let open Cat in record
           { Obj = Obj C × Obj D
           ; Hom = λ X Y →  Hom C (fst X) (fst Y) × Hom D (snd X) (snd Y)
           ; iden = (iden C) , (iden D)
           ; _∙_ = λ f g → (_∙_ C (fst f) (fst g)) , (_∙_ D (snd f) (snd g))
           ; idl = cong₂ _,_ (idl C) (idl D)
           ; idr = cong₂ _,_ (idr C) (idr D)
           ; ass = cong₂ _,_ (ass C) (ass D)
           }

--------------------------------------------------
{- Familia de Conjuntos -}
{- Los objetos son familias de conjuntos
   (conjuntos indexados por un conjunto de índices)

  Los morfismos son funciones que preservan el índice.
-}

Fam : Set → Cat
Fam I = record
          { Obj = I → Set
          ; Hom = λ X Y → ∀{i} → X i → Y i 
          ; iden = id
          ; _∙_ = λ f g → f ∘ g
          ; idl = refl
          ; idr = refl
          ; ass = refl
          }

--------------------------------------------------
{- Ejemplo extendido: Categorías Slice -}

{- Dada una categoría C, los objetos de un slice
   sobre un objeto I, son morfismos con codominio I
-}

module Slice (C : Cat) where

 open Cat C

 record Slice₀ (I : Obj) : Set₁ where
  constructor _,_
  field
     base : Obj
     morObj : Hom base I

 open Slice₀

 {- record para representar los morfismos de la categoría -}
 record Slice₁ (I : Obj)(X Y : Slice₀ I) : Set where
  constructor _,_
  field
    baseHom : Hom (base X) (base Y)
    prop :  (morObj Y) ∙ baseHom ≅ morObj X
      
     {- para probar que dos morfismos de slice son iguales no nos
        interesa cual es la prueba de pro.  Cualquier prueba es
        suficiente
     -}

 open Slice₁

 {- veamos como funciona proof irrelevance -}
 Slice₁-eq : {I : Obj}{X Y : Slice₀ I}
          → {f g : Slice₁ I X Y}
          → baseHom f ≅ baseHom g
          → f ≅ g
 Slice₁-eq {f = f , p} {.f , q} refl = cong (_,_ f) (ir p q)


 {- la composición es simplemente pegar triángulos -}
 Slice-comp : {I : Obj}
             → {X Y Z :  Slice₀ I}
             → Slice₁ I Y Z --Hom Y Z
             → Slice₁ I X Y --Hom X Y
             → Slice₁ I X Z --Hom X Z
 Slice-comp {X = X , fx} {Y , fy} {Z , fz} (f , p) (g , q) =
                      (f ∙ g) , (proof
                      fz ∙ (f ∙ g)
                      ≅⟨ sym ass ⟩
                      (fz ∙ f) ∙ g
                      ≅⟨ cong₂ _∙_ p refl ⟩
                      fy ∙ g
                      ≅⟨ q ⟩
                      fx
                      ∎)


 Slice : (I : Obj) → Cat
 Slice I = record
              { Obj = Slice₀ I
              ; Hom = Slice₁ I
              ; iden = iden , idr
              ; _∙_ = Slice-comp
              ; idl = Slice₁-eq idl
              ; idr = Slice₁-eq idr
              ; ass = Slice₁-eq ass
              }

--------------------------------------------------

{- Ejercicio: Definir la categoría con un sólo objeto ⊤, y que sus
morfismos son los elementos de un monoide M -}

module catUnit where 
 
 open import Records hiding (⊤)

 CatUnit : (M : Monoid) → Cat
 CatUnit M = let open Monoid M in
              record
               { Obj = Lift ⊤
               ; Hom = λ x y → Carrier
               ; iden = λ {x} → ε
               ; _∙_ = λ x y →  x ∙ y
               ; idl = lid
               ; idr = rid
               ; ass = assoc
               }


--------------------------------------------------
{- Ejercicio: Definir la categoría en que los objetos son monoides,
  y las flechas son homomorfismos de monoides
-}

module MonCat where

 open import Records hiding (Iso)

 open Monoid
 open Monoid-Homomorphism

 record catMonoid₁ (M N : Monoid) : Set where
  constructor _,_
  field
     morp : Carrier M → Carrier N
     is-homo : Is-Monoid-Homo {M} {N} morp

 lemaCatMonoid1 : {M : Monoid} → Is-Monoid-Homo {M} {M} id
 lemaCatMonoid1 = record { preserves-unit = refl ; preserves-mult = refl }


 compCatMonoid : {X Y Z : Monoid} → catMonoid₁ Y Z → catMonoid₁ X Y → catMonoid₁ X Z
 compCatMonoid {X} {Y} {Z} (morp₁ , is-homo₁) (morp₂ , is-homo₂) = (morp₁ ∘ morp₂) ,
                            ((proof 
                              (morp₁ ∘ morp₂) (ε X) 
                              ≅⟨ cong (λ x → morp₁ x) (preserves-unit is-homo₂) ⟩ 
                              morp₁ (ε Y) 
                              ≅⟨ preserves-unit is-homo₁ ⟩ 
                              ε Z ∎) ,
                            (λ {x} {y} → proof 
                             (morp₁ ∘ morp₂) (x ∙₁ y) 
                             ≅⟨ cong (λ x₁ → morp₁ x₁) (preserves-mult is-homo₂) ⟩ 
                             morp₁ (morp₂ x ∙₂ morp₂ y) 
                             ≅⟨ preserves-mult is-homo₁ ⟩ 
                             ((morp₁ ∘ morp₂) x) ∙₃ ((morp₁ ∘ morp₂) y) ∎))
                            where open Monoid X renaming (ε to ε₁ ;  _∙_ to _∙₁_)
                                  open Monoid Y renaming (ε to ε₂ ;  _∙_ to _∙₂_)
                                  open Monoid Z renaming (ε to ε₂ ;  _∙_ to _∙₃_)
                                  open Is-Monoid-Homo

 open catMonoid₁

 lemaCatMonid-eq : {M N : Monoid} {f : Carrier M → Carrier N} → 
                 (a b : Is-Monoid-Homo {M} {N} f) → a ≅ b
 lemaCatMonid-eq a b = let open Is-Monoid-Homo in
                       cong₂ (Is-Monoid-Homo._,_) (ir (preserves-unit a) (preserves-unit b))
                         (i2ir (preserves-mult a) (preserves-mult b))


 catMonoid-eq : {X Y : Monoid} {f g : catMonoid₁ X Y } → morp f ≅ morp g → f ≅ g
 catMonoid-eq {f = f , f-is-homo} {.f , g-is-homo} refl = cong (λ x → f , x) (lemaCatMonid-eq f-is-homo g-is-homo)

 catMonoid : Cat
 catMonoid = record
                    { Obj = Monoid
                    ; Hom = catMonoid₁
                    ; iden = id , lemaCatMonoid1
                    ; _∙_ = compCatMonoid
                    ; idl = catMonoid-eq refl
                    ; idr = catMonoid-eq refl
                    ; ass = catMonoid-eq refl
                    }

--------------------------------------------------
{- Ejercicio: Dada un categoría C, definir la siguiente categoría:
  - Los objetos son morfismos de C
  - Un morfismo entre una flecha f: A → B y f': A'→ B' es un par de morfismos de C
      g1 : A → A', y g2 : B → B', tal que
                    f' ∙ g₁ ≅ g₂ ∙ f
-}

module CMorphs (C : Cat) where

 open Cat C

 --open import Records hiding (Iso)

 record catMorphs₀ : Set₁ where
  constructor catObj
  field
   base₁ : Obj
   base₂ : Obj
   obj : Hom base₁ base₂

 record catMorphs₁ (X Y : catMorphs₀) : Set where
  constructor catMorp
  open catMorphs₀
  field
   morp₁ : Hom (base₁ X) (base₁ Y) 
   morp₂ : Hom (base₂ X) (base₂ Y)
   prop :  morp₂ ∙ (obj X) ≅ (obj Y) ∙ morp₁

 idenCatMorphs : (X : catMorphs₀) → catMorphs₁ X X
 idenCatMorphs (catObj b₁ b₂ o) = catMorp iden iden
                                  (proof
                                   iden ∙ o
                                   ≅⟨ idl ⟩
                                   o
                                   ≅⟨ sym idr ⟩
                                   o ∙ iden ∎)


 compCatMorphs : {X Y Z : catMorphs₀} → catMorphs₁ Y Z → catMorphs₁ X Y → catMorphs₁ X Z
 compCatMorphs {catObj b₁ b₂ obj} {catObj b₃ b₄ obj₁} {catObj b₅ b₆ obj₂}
   (catMorp g₃ g₄ prop₂) (catMorp g₁ g₂ prop₁) =
     catMorp (g₃ ∙ g₁) (g₄ ∙ g₂)
       (proof
       (g₄ ∙ g₂) ∙ obj
       ≅⟨ ass ⟩
       g₄ ∙ (g₂ ∙ obj)
       ≅⟨ cong (λ x → g₄ ∙ x) prop₁ ⟩
       g₄ ∙ (obj₁ ∙ g₁)
       ≅⟨ sym ass ⟩
       (g₄ ∙ obj₁) ∙ g₁
       ≅⟨ cong (λ x → x ∙ g₁) prop₂ ⟩
       (obj₂ ∙ g₃) ∙ g₁
       ≅⟨ ass ⟩
       obj₂ ∙ (g₃ ∙ g₁) ∎ )


 open catMorphs₀
 open catMorphs₁

 catMorphs-eq : {X Y : catMorphs₀} {f g : catMorphs₁ X Y} → morp₁ f ≅ morp₁ g →
   morp₂ f ≅ morp₂ g → f ≅ g
 catMorphs-eq {catObj b₁ b₂ obj} {catObj b₃ b₄ obj₁} {catMorp m₁ m₂ prop} {catMorp m₃ m₄ prop₁}
   x y = cong₃ catMorp x y (ir2
     ( (proof
        m₂ ∙ obj
        ≅⟨ cong (λ w → w ∙ obj) y ⟩
        m₄ ∙ obj ∎ )
     )
     (proof
      obj₁ ∙ m₁
      ≅⟨ cong (λ w → obj₁ ∙ w) x ⟩
      obj₁ ∙ m₃ ∎)
     prop
     prop₁)


 catMorphs : Cat
 catMorphs = record
             { Obj = catMorphs₀
               ; Hom = λ x y → catMorphs₁ x y 
               ; iden = λ {x} → idenCatMorphs x
               ; _∙_ = compCatMorphs
               ; idl = catMorphs-eq idl idl
               ; idr = catMorphs-eq idr idr
               ; ass = catMorphs-eq ass ass
              }
              
--------------------------------------------------
{- Generalizamos la noción de isomorfismo de la clase pasada a cualquier categoría -}

{- Isomorfismo en una categoría -}

open Cat

record Iso {C : Cat}(A B : Obj C)(fun : Hom C A B) : Set where
  constructor iso
  field inv : Hom C B A
        law1 : _∙_ C fun inv  ≅ iden C {B}
        law2 : _∙_ C inv fun  ≅ iden C {A}

--------------------------------------------------

{- Ejercicio
 Mostrar que en el caso de la categoría Sets, isomorfismo corresponde a biyección de funciones

Ayuda : puede ser útil usar cong-app
-}

Biyectiva : {X Y : Set}(f : X → Y) → Set
Biyectiva {X} {Y} f = (y : Y) → Σ X (λ x → (f x ≅ y) × (∀ x' → f x' ≅ y → x ≅ x')) 

isoSets→ : {X Y : Set} {f : X → Y} → Iso {Sets} X Y f → Biyectiva f
isoSets→ {f = f} (iso inv l₁ l₂) y = (inv y) , ((cong-app l₁ y) , (λ x' x →
                                     proof inv y
                                     ≅⟨ cong (λ w → inv w) (sym x) ⟩
                                     inv (f x')
                                     ≅⟨ cong-app l₂ x' ⟩
                                     x' ∎))

-- Se puede probar?
-- isoSets← : {X Y : Set} {f : X → Y} → Biyectiva f → Iso {Sets} X Y f
-- isoSets← {f = f} x = {!!}

--------------------------------------------------
{- Ejercicio:
 Probar que un isormofismo en (C : Cat) es un isomorfismo en (C Op).
-}

isoCDual→ : {C : Cat} {A B : Obj C} {f : Hom C A B} → Iso {C} A B f → Iso {C Op} B A f
isoCDual→ (iso inv l₁ l₂) = iso inv l₂ l₁

isoCDual← : {C : Cat} {A B : Obj C} {f : Hom C A B} → Iso {C Op} B A f → Iso {C} A B f
isoCDual← (iso inv l₁ l₂) = iso inv l₂ l₁

--------------------------------------------------
{- Ejercicio EXTRA:
 Definir la categoría de pointed sets:
  - objetos son conjuntos junto con un elemento designado del conjunto.
     Por ejemplo (Bool , false), (ℕ , 0) , etc.
  - los morfismos son funciones entre los conjuntos que preservan el punto
     (A,a) → (B, b) es una función f : A → B, tal que f(a) = b 
-}

module CatPointedSets where

 record CatPS₀ : Set₁ where
   constructor obj
   field conj : Set
         elem : conj

 record CatPS₁ (X Y : CatPS₀) : Set₀ where
   constructor morp
   open CatPS₀
   field fun : conj X → conj Y
         prop : fun (elem X) ≅ elem Y
         

 idenCatPS : {X : CatPS₀} → CatPS₁ X X
 idenCatPS {obj c e} = morp id refl

 compCatPS : {X Y Z : CatPS₀} → CatPS₁ Y Z → CatPS₁ X Y → CatPS₁ X Z
 compCatPS {obj conj a} {obj conj₁ b} {obj conj₂ c} (morp g p₂) (morp f p₁) =
   morp (g ∘ f) (
     proof (g ∘ f) a
     ≅⟨ refl ⟩
     g (f a)
     ≅⟨ cong (λ x → g x) p₁ ⟩
     g b
     ≅⟨ p₂ ⟩
     c ∎)

 open CatPS₁
 
 compCat-eq : {X Y : CatPS₀} {f g : CatPS₁ X Y} → fun f ≅ fun g → f ≅ g
 compCat-eq {obj conj a} {obj conj₁ b} {morp f p₁} {morp g p₂} x =
   cong₂ morp x (ir2 (cong-app x a) refl p₁ p₂)

 CatPS : Cat
 CatPS = record
           { Obj = CatPS₀
           ; Hom = CatPS₁
           ; iden = idenCatPS
           ; _∙_ = compCatPS
           ; idl = compCat-eq refl
           ; idr = compCat-eq refl
           ; ass = compCat-eq refl
           }

--------------------------------------------------

{- Ejercicio EXTRA:
 Definir la categoría cuyos
  - objetos son conjuntos finitos (y por lo tanto isomorfos a Fin n para algún n)
  - morfismos son isomorfismos.  
-}


module CatFin where

  record catFin₀ : Set₁ where
    constructor obj
    field size : ℕ
--          conj : Fin size

  record catFin₁ (X Y : catFin₀) : Set where
    constructor morp
    open catFin₀
    field fun : Fin (size X) → Fin (size Y)
          prop : Iso {Sets} (Fin (size X)) (Fin (size Y)) fun


  idenCatFin : {X : catFin₀} → catFin₁ X X
  idenCatFin {obj n} = morp id (iso id refl refl)

  compCatFin : {X Y Z : catFin₀} → catFin₁ Y Z → catFin₁ X Y → catFin₁ X Z
  compCatFin {obj n} {obj n₁} {obj n₂} (morp g (iso g⁻¹ lg₁ lg₂)) (morp f (iso f⁻¹ lf₁ lf₂)) =
    morp (g ∘ f) (iso (f⁻¹ ∘ g⁻¹)
      (proof (g ∘ f) ∘ (f⁻¹ ∘ g⁻¹)
        ≅⟨ ass Sets {f = g} {g = f} {h = f⁻¹ ∘ g⁻¹}⟩
        g ∘ (f ∘ f⁻¹ ∘ g⁻¹)
        ≅⟨ cong (λ x → g ∘ x) (sym (ass Sets {f = f} {g = f⁻¹} {h = g⁻¹})) ⟩
        g ∘ (f ∘ f⁻¹) ∘ g⁻¹
        ≅⟨ cong (λ x → g ∘ x ∘ g⁻¹) lf₁ ⟩
        g ∘ id ∘ g⁻¹
        ≅⟨ refl ⟩
        g ∘ g⁻¹
        ≅⟨ lg₁ ⟩
        id ∎)
       (proof
          (f⁻¹ ∘ g⁻¹) ∘ (g ∘ f)
          ≅⟨ ass Sets {f = f⁻¹} {g = g⁻¹} {h = g ∘ f} ⟩
          f⁻¹ ∘ (g⁻¹ ∘ (g ∘ f))
          ≅⟨ cong (λ x → f⁻¹ ∘ x) (sym (ass Sets {f = g⁻¹} {g = g} {h = f})) ⟩
          f⁻¹ ∘ ((g⁻¹ ∘ g) ∘ f)
          ≅⟨ cong (λ x → f⁻¹ ∘ x ∘ f) lg₂ ⟩
          f⁻¹ ∘ id ∘ f
          ≅⟨ refl ⟩
          f⁻¹ ∘ f
          ≅⟨ lf₂ ⟩
          id ∎))


  open catFin₁
  open Iso

  lemaCatFin : {n m : ℕ} {fun : Fin n → Fin m} → (f g : Iso {Sets} (Fin n) (Fin m) fun) → f ≅ g
  lemaCatFin (iso f⁻¹ lf₁ lf₂) (iso g⁻¹ lg₁ lg₂) = cong₃ iso {!!} {!!} {!!}
  

  catFin-eq : {X Y : catFin₀} → (f g : catFin₁ X Y) → fun f ≅ fun g → f ≅ g
  catFin-eq (morp f prop) (morp g prop₁) x = cong₂ morp x {!!}
  
          

  catFin : Cat
  catFin = record
             { Obj = catFin₀
             ; Hom = catFin₁
             ; iden = idenCatFin
             ; _∙_ = compCatFin
             ; idl = {!!}
             ; idr = {!!}
             ; ass = {!!}
             }









--------------------------------------------------
