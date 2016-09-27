
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
  TerminalIso T T' p q =
    iso (t q {T})
        (proof
          t p ∙ t q 
          ≅⟨ sym (law p {f = t p ∙ t q} ) ⟩
          t p 
          ≅⟨ law p {f = iden} ⟩ 
          iden ∎) 
        (proof
          t q ∙ t p 
          ≅⟨ sym (law q) ⟩ 
          t q 
          ≅⟨ law q ⟩ 
          iden ∎)

module SetStructure {l : Level} where

 open import Categories.Sets
{- Ejercicios
   -- Probar que Sets tiene objeto terminal y productos
-}
 SetsHasProducts : Products (Sets {l}) 
 SetsHasProducts = prod
                   Library._×_ 
                   fst 
                   snd 
                   (λ f g x → f x , g x) 
                   refl 
                   refl 
                   (λ {_} {_} {_} {f} {g} {h} p₁ p₂ → ext (λ c →
                     proof
                     h c
                     ≅⟨ refl ⟩ 
                     fst (h c) , snd (h c) 
                     ≅⟨ cong (λ x → x , snd (h c)) (cong-app p₁ c) ⟩ 
                     f c , snd (h c) 
                     ≅⟨ cong (λ x → f c , x) (cong-app p₂ c) ⟩ 
                     f c , g c ∎))

 open import Data.Unit.Base
 
 OneSet : Terminal Sets ⊤
 OneSet = term (λ x → ⊤.tt) refl

{- Ejercicio EXTRA: Analizar si la categoría de pointed sets
   tiene producto y objeto terminal, en cuyo caso definirlo
-}


{- Dos productos de los mismos objetos son isomorfos -}
module ProductIso {a}{b}(C : Cat {a}{b}) where

  open Cat C

  open Products

  ProductIso : ∀{A B} → (p q : Products C)
           → Iso C (⟨_,_⟩ p {A} {B} (π₁ q) (π₂ q))
  ProductIso {A} {B} p q = iso
                   (⟨_,_⟩ q (π₁ p) (π₂ p)) 
                   (sym (proof
                     iden {_×_ p A B }
                     ≅⟨ law3 p {f = π₁ p} {π₂ p} (idr) (idr) ⟩
                     ⟨_,_⟩ p (π₁ p) (π₂ p)
                     ≅⟨ sym (law3 p
                            ((proof
                              π₁ p ∙ ((⟨_,_⟩ p (π₁ q) (π₂ q)) ∙ (⟨_,_⟩ q (π₁ p) (π₂ p)))
                              ≅⟨ sym ass ⟩
                              (π₁ p ∙ (⟨_,_⟩ p (π₁ q) (π₂ q))) ∙ (⟨_,_⟩ q (π₁ p) (π₂ p))
                              ≅⟨ cong (λ x → x ∙ (⟨_,_⟩ q (π₁ p) (π₂ p))) (law1 p) ⟩
                              π₁ q ∙ (⟨_,_⟩ q (π₁ p) (π₂ p))
                              ≅⟨ law1 q ⟩
                              π₁ p ∎))
                            (proof
                              π₂ p ∙ ((⟨_,_⟩ p (π₁ q) (π₂ q)) ∙ (⟨_,_⟩ q (π₁ p) (π₂ p)))
                              ≅⟨ sym ass ⟩
                              (π₂ p ∙ (⟨_,_⟩ p (π₁ q) (π₂ q))) ∙ (⟨_,_⟩ q (π₁ p) (π₂ p)) 
                              ≅⟨ cong (λ x → x ∙ (⟨_,_⟩ q (π₁ p) (π₂ p))) (law2 p) ⟩
                              π₂ q ∙ (⟨_,_⟩ q (π₁ p) (π₂ p))
                              ≅⟨ law2 q ⟩
                              π₂ p ∎)) ⟩
                     (⟨_,_⟩ p (π₁ q) (π₂ q)) ∙ (⟨_,_⟩ q (π₁ p) (π₂ p)) ∎))
                   (sym (proof
                     iden
                     ≅⟨ law3 q idr idr ⟩
                     ⟨_,_⟩ q (π₁ q) (π₂ q)
                     ≅⟨ sym (law3 q
                            (proof
                              π₁ q ∙ ((⟨_,_⟩ q (π₁ p) (π₂ p)) ∙ (⟨_,_⟩ p (π₁ q) (π₂ q)))
                              ≅⟨ sym ass ⟩
                              (π₁ q ∙ (⟨_,_⟩ q (π₁ p) (π₂ p))) ∙ (⟨_,_⟩ p (π₁ q) (π₂ q))
                              ≅⟨ cong (λ x → x ∙ (⟨_,_⟩ p (π₁ q) (π₂ q))) (law1 q) ⟩
                              π₁ p ∙ (⟨_,_⟩ p (π₁ q) (π₂ q))
                              ≅⟨ law1 p ⟩
                              π₁ q ∎)
                            (proof
                              π₂ q ∙ ((⟨_,_⟩ q (π₁ p) (π₂ p)) ∙ (⟨_,_⟩ p (π₁ q) (π₂ q)))
                              ≅⟨ sym ass ⟩
                              (π₂ q ∙ (⟨_,_⟩ q (π₁ p) (π₂ p))) ∙ (⟨_,_⟩ p (π₁ q) (π₂ q)) 
                              ≅⟨ cong (λ x → x ∙ (⟨_,_⟩ p (π₁ q) (π₂ q))) (law2 q) ⟩
                              π₂ p ∙ (⟨_,_⟩ p (π₁ q) (π₂ q))
                              ≅⟨ law2 p ⟩
                              π₂ q ∎)) ⟩
                     (⟨_,_⟩ q (π₁ p) (π₂ p)) ∙ (⟨_,_⟩ p (π₁ q) (π₂ q)) ∎))


module ProductMorphisms {a}{b}{C : Cat {a}{b}}(p : Products C) where

  open Cat C
  open Products p

  {- Toda categoría con productos posee los siguientes morfismos -}
  swap : ∀{A B} → Hom (A × B)  (B × A)
  swap = {!!}

  assoc : ∀{A B C} → Hom ((A × B) × C) (A × (B × C))
  assoc = {!!}

  -- Probar que swap y assoc son isomorfismos.


  {- Definir el morfismo pair -}
  pair : ∀{A B C D}(f : Hom A B)(g : Hom C D)
       → Hom (A × C) (B × D)
  pair f g = {!!}

  -- Probar las siguientes propiedades de pair

  idpair : ∀{X} → pair (iden {X}) (iden {X}) ≅ iden {X × X}
  idpair {X} = {!!}

  compdistrib : ∀{A B C D E F}
              → (f : Hom B C)(g : Hom A B)
              → (h : Hom E F)(i : Hom D E)
              → pair (f ∙ g) (h ∙ i) ≅ pair f h ∙ pair g i
  compdistrib f g h i = {!!}

  open import Categories.ProductCat
  open import Functors

  -- Probar que el producto de objetos _×_, junto con pair
  -- forman un funtor C ×C C → C
  
--------------------------------------------------

