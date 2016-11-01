
module Construcciones where

open import Library hiding (_×_ ; swap)
open import Categories
open import Categories.Products
open import Categories.Terminal

open import Categories.Iso

module TerminalIso {a}{b}(C : Cat {a}{b}) where
  open Terminal
  open Cat C

  {- Dos objetos terminales son isomorfos -}
  TerminalIso : (T T' : Obj)
            → (p : Terminal C T)
            → (q : Terminal C T')
            → Iso C (t p {T'})
  TerminalIso T T' p q = iso (t q) (trans (sym (law p)) (law p)) (trans (sym (law q)) (law q))

module SetStructure {l : Level} where

 open import Categories.Sets
{- Ejercicios
   -- Probar que Sets tiene objeto teminal y productos
-}
{-
 SetsHasProducts : Products (Sets {l}) 
 SetsHasProducts = {!!}

 OneSet : Terminal Sets ⊤
 OneSet = {!!}
-}

{- Ejercicio EXTRA: Analizar si la categoría de pointed sets
   tiene producto y objeto terminal, en cuyo caso definirlo
-}


{- Dos productos de los mismos objetos son isomorfos -}
module ProductIso {a}{b}(C : Cat {a}{b}) where

  open Cat C

  open Products

  ProductIso : ∀{A B} → (p q : Products C)
           → Iso C (⟨_,_⟩ p {A} {B} (π₁ q) (π₂ q))
  ProductIso p q = iso (⟨_,_⟩ q (π₁ p) (π₂ p))
                      (proof
                      ⟨_,_⟩ p (π₁ q) (π₂ q) ∙ ⟨_,_⟩ q (π₁ p) (π₂ p)
                      ≅⟨ law3 p (trans (sym ass) (trans (cong₂ _∙_ (law1 p) refl) (law1 q)))
                                (trans (sym ass) (trans (cong₂ _∙_ (law2 p) refl) (law2 q))) ⟩
                      ⟨_,_⟩ p (π₁ p)  (π₂ p)
                      ≅⟨ sym (law3 p idr idr) ⟩
                      iden
                      ∎)
                      (proof
                      ⟨ q , π₁ p ⟩ (π₂ p) ∙ ⟨ p , π₁ q ⟩ (π₂ q)
                      ≅⟨ law3 q (trans (sym ass) (trans (cong₂ _∙_ (law1 q) refl) (law1 p)))
                                (trans (sym ass) (trans (cong₂ _∙_ (law2 q) refl) (law2 p))) ⟩
                       ⟨ q , π₁ q ⟩ (π₂ q)
                      ≅⟨ sym (law3 q idr idr) ⟩
                      iden
                      ∎)

module ProductMorphisms {a}{b}{C : Cat {a}{b}}(p : Products C) where

  open Cat C
  open Products p

  {- Toda categoría con productos posee los siguientes morfismos -}
  swap : ∀{A B} → Hom (A × B)  (B × A)
  swap = ⟨ π₂ , π₁ ⟩

  assoc : ∀{A B C} → Hom ((A × B) × C) (A × (B × C))
  assoc = ⟨ (π₁ ∙ π₁) , ⟨ (π₂ ∙ π₁) , π₂ ⟩ ⟩
  
  -- Probar que swap y assoc son isomorfismos.


  {- Definir el morfismo pair -}
  pair : ∀{A B C D}(f : Hom A B)(g : Hom C D)
       → Hom (A × C) (B × D)
  pair f g = ⟨ f ∙ π₁ , g ∙ π₂ ⟩

  -- Probar las siguientes propiedades de pair

  idpair : ∀{X Y} → pair (iden {X}) (iden {Y}) ≅ iden {X × Y}
  idpair {X}{Y}  =  (sym (law3 (trans idr (sym idl))
                         (trans idr (sym idl))))

  compdistrib : ∀{A B C D E F}
              → (f : Hom B C)(g : Hom A B)
              → (h : Hom E F)(i : Hom D E)
              → pair (f ∙ g) (h ∙ i) ≅ pair f h ∙ pair g i
  compdistrib f g h i = proof
                  pair (f ∙ g) (h ∙ i)
                 ≅⟨ cong₂ ⟨_,_⟩ ass ass ⟩
                  ⟨ f ∙ g ∙ π₁ , h ∙ i ∙ π₂ ⟩ 
                 ≅⟨ cong₂ (λ x y → ⟨ _∙_ f x , _∙_ h y ⟩) (sym law1) (sym law2) ⟩
                  ⟨ f ∙ (π₁ ∙ pair g i) , h ∙ (π₂ ∙ pair g i) ⟩ 
                 ≅⟨ cong₂ ⟨_,_⟩ (sym ass) (sym ass) ⟩
                  ⟨ (f ∙ π₁) ∙ pair g i , (h ∙ π₂) ∙ pair g i ⟩ 
                 ≅⟨ cong₂ (λ x y → ⟨ _∙_ x (pair g i) , _∙_ y (pair g i) ⟩) (sym law1) (sym law2) ⟩
                  ⟨ (π₁ ∙ pair f h) ∙ pair g i , (π₂ ∙ pair f h) ∙ pair g i ⟩ 
                 ≅⟨ cong₂ ⟨_,_⟩ ass ass ⟩
                  ⟨ π₁ ∙ (pair f h ∙ pair g i) , π₂ ∙ (pair f h ∙ pair g i) ⟩ 
                 ≅⟨ sym (law3 refl refl) ⟩
                  pair f h ∙ pair g i
                 ∎ 

  open import Categories.ProductCat
  open import Functors

  -- Probar que el producto de objetos _×_, junto con pair
  -- forman un funtor C ×C C → C
  
--------------------------------------------------

