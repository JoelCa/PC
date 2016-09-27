module Categories.Arrow where

open import Library
open import Categories

--------------------------------------------------

{- Dada un categoría C, la categoría Arrow es la siguiente categoría:
  - Los objetos son morfismos de C
  - Un morfismo entre una flecha f: A → B y f': A'→ B' es un par de morfismos de C
      g1 : A → A', y g2 : B → B', tal que
                    f' ∙ g₁ ≅ g₂ ∙ f
-}

module ArrowCat {a}{b}(C : Cat {a}{b}) where

 open Cat C 

 record Arrow₀ : Set (a ⊔ b) where
    field source : Obj
          target : Obj
          obj : Hom source target
          
 open Arrow₀

 record Arrow₁ (A B : Arrow₀) : Set b where
    constructor _,_
    field morph : Hom (source A) (source B) × Hom (target A) (target B)
          prop  : obj B ∙ fst morph ≅ snd morph ∙ obj A  

 open Arrow₁

 Arrow₁Eq : ∀{A B}{f g : Arrow₁ A B}
          → fst (morph f) ≅ fst (morph g)
          → snd (morph f) ≅ snd (morph g)
          → f ≅ g
 Arrow₁Eq {f = f , p} { .f , q} refl refl = cong (_,_ f) (ir p q)

 ArrowIden : (f : Arrow₀) →  Arrow₁ f f
 ArrowIden f = (iden , iden) , (trans idr (sym idl))

 ArrowComp : (X Y Z : Arrow₀) →
             Arrow₁ Y Z → Arrow₁ X Y → Arrow₁ X Z
 ArrowComp X Y Z ((f₁ , f₂) , p) ((g₁ , g₂) , q) = ((f₁ ∙ g₁) , (f₂ ∙ g₂)) , (
                     proof
                     obj Z ∙ f₁ ∙ g₁
                     ≅⟨ trans (sym ass) (cong (λ x → _∙_ x g₁) p) ⟩
                     (f₂ ∙ obj Y) ∙ g₁
                     ≅⟨ trans ass (cong (_∙_ f₂) q) ⟩
                     f₂ ∙ (g₂ ∙ obj X)
                     ≅⟨ sym ass ⟩
                     (f₂ ∙ g₂) ∙ obj X
                     ∎
                     )

 ArrowCat : Cat
 ArrowCat = record
               { Obj = Arrow₀
               ; Hom = Arrow₁
               ; iden = λ {f} → ArrowIden f
               ; _∙_ = λ {x} {y} {z} → ArrowComp x y z
               ; idl = Arrow₁Eq idl idl
               ; idr = Arrow₁Eq idr idr
               ; ass = Arrow₁Eq ass ass
               }
               
open ArrowCat public
