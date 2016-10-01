

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
  swap = λ {A} {B} → ⟨_,_⟩ {B} {A} (π₂ {A} {B}) (π₁ {A} {B})

  assoc : ∀{A B C} → Hom ((A × B) × C) (A × (B × C))
  assoc = ⟨ π₁ ∙ π₁ , ⟨ π₂ ∙ π₁ , π₂ ⟩ ⟩

  -- Probar que swap y assoc son isomorfismos.
  swapIso : ∀{A B} → Iso C (swap {A} {B})
  swapIso = iso (⟨_,_⟩ π₂ π₁)
                (sym (proof
                        iden
                        ≅⟨ law3 idr idr ⟩
                        ⟨ π₁ , π₂ ⟩
                        ≅⟨ sym (law3 (proof
                                     π₁ ∙ (⟨ π₂ , π₁ ⟩ ∙ ⟨ π₂ , π₁ ⟩)
                                     ≅⟨ sym ass ⟩
                                     ( π₁ ∙ ⟨ π₂ , π₁ ⟩) ∙ ⟨ π₂ , π₁ ⟩
                                     ≅⟨ cong (λ x → x ∙ ⟨ π₂ , π₁ ⟩) law1 ⟩
                                     π₂ ∙ ⟨ π₂ , π₁ ⟩
                                     ≅⟨ law2 ⟩
                                     π₁ ∎)
                                     (proof
                                       π₂ ∙ (⟨ π₂ , π₁ ⟩ ∙ ⟨ π₂ , π₁ ⟩)
                                       ≅⟨ sym ass ⟩
                                       ( π₂ ∙ ⟨ π₂ , π₁ ⟩) ∙ ⟨ π₂ , π₁ ⟩
                                       ≅⟨ cong (λ x → x ∙ ⟨ π₂ , π₁ ⟩) law2 ⟩
                                       π₁ ∙ ⟨ π₂ , π₁ ⟩
                                       ≅⟨ law1 ⟩
                                       π₂ ∎) )⟩
                        ⟨ π₂ , π₁ ⟩ ∙ ⟨ π₂ , π₁ ⟩ ∎))
                (sym (proof
                     iden
                     ≅⟨ law3 idr idr ⟩
                     ⟨ π₁ , π₂ ⟩
                     ≅⟨ sym (law3 (proof
                                     π₁ ∙ (⟨ π₂ , π₁ ⟩ ∙ ⟨ π₂ , π₁ ⟩)
                                     ≅⟨ sym ass ⟩
                                     ( π₁ ∙ ⟨ π₂ , π₁ ⟩) ∙ ⟨ π₂ , π₁ ⟩
                                     ≅⟨ cong (λ x → x ∙ ⟨ π₂ , π₁ ⟩) law1 ⟩
                                     π₂ ∙ ⟨ π₂ , π₁ ⟩
                                     ≅⟨ law2 ⟩
                                     π₁ ∎)
                                     (proof
                                       π₂ ∙ (⟨ π₂ , π₁ ⟩ ∙ ⟨ π₂ , π₁ ⟩)
                                       ≅⟨ sym ass ⟩
                                       ( π₂ ∙ ⟨ π₂ , π₁ ⟩) ∙ ⟨ π₂ , π₁ ⟩
                                       ≅⟨ cong (λ x → x ∙ ⟨ π₂ , π₁ ⟩) law2 ⟩
                                       π₁ ∙ ⟨ π₂ , π₁ ⟩
                                       ≅⟨ law1 ⟩
                                       π₂ ∎) )⟩
                     ⟨ π₂ , π₁ ⟩ ∙ ⟨ π₂ , π₁ ⟩ ∎))

  assocIso : ∀{A B D} → Iso C (assoc {A} {B} {D})
  assocIso = iso (⟨ ⟨ π₁ , π₁ ∙ π₂ ⟩ , π₂ ∙ π₂ ⟩)
                 (sym (proof
                      iden
                      ≅⟨ law3 idr idr ⟩
                      ⟨ π₁ , π₂ ⟩
                      ≅⟨ sym (law3 (proof
                                   π₁ ∙ (⟨ π₁ ∙ π₁ , ⟨ π₂ ∙ π₁ , π₂ ⟩ ⟩
                                          ∙ ⟨ ⟨ π₁ , π₁ ∙ π₂ ⟩ , π₂ ∙ π₂ ⟩)
                                   ≅⟨ sym ass ⟩
                                   (π₁ ∙ ⟨ π₁ ∙ π₁ , ⟨ π₂ ∙ π₁ , π₂ ⟩ ⟩)
                                    ∙ ⟨ ⟨ π₁ , π₁ ∙ π₂ ⟩ , π₂ ∙ π₂ ⟩ 
                                   ≅⟨ cong (λ x → x ∙ ⟨ ⟨ π₁ , π₁ ∙ π₂ ⟩ , π₂ ∙ π₂ ⟩) law1 ⟩
                                   (π₁ ∙ π₁) ∙ ⟨ ⟨ π₁ , π₁ ∙ π₂ ⟩ , π₂ ∙ π₂ ⟩
                                   ≅⟨ ass ⟩
                                   π₁ ∙ (π₁ ∙ ⟨ ⟨ π₁ , π₁ ∙ π₂ ⟩ , π₂ ∙ π₂ ⟩)
                                   ≅⟨ cong (λ x → π₁ ∙ x) law1 ⟩
                                   π₁ ∙ ⟨ π₁ , π₁ ∙ π₂ ⟩
                                   ≅⟨ law1 ⟩
                                   π₁ ∎)
                                   (proof
                                     π₂ ∙ (⟨ π₁ ∙ π₁ , ⟨ π₂ ∙ π₁ , π₂ ⟩ ⟩
                                             ∙ ⟨ ⟨ π₁ , π₁ ∙ π₂ ⟩ , π₂ ∙ π₂ ⟩)
                                     ≅⟨ sym ass ⟩
                                     (π₂ ∙ ⟨ π₁ ∙ π₁ , ⟨ π₂ ∙ π₁ , π₂ ⟩ ⟩)
                                       ∙ ⟨ ⟨ π₁ , π₁ ∙ π₂ ⟩ , π₂ ∙ π₂ ⟩ 
                                     ≅⟨ cong (λ x → x ∙ ⟨ ⟨ π₁ , π₁ ∙ π₂ ⟩ , π₂ ∙ π₂ ⟩) law2 ⟩
                                     ⟨ π₂ ∙ π₁ , π₂ ⟩ ∙ ⟨ ⟨ π₁ , π₁ ∙ π₂ ⟩ , π₂ ∙ π₂ ⟩
                                     ≅⟨ law3 (proof
                                             π₁ ∙ (⟨ π₂ ∙ π₁ , π₂ ⟩
                                                     ∙ ⟨ ⟨ π₁ , π₁ ∙ π₂ ⟩ , π₂ ∙ π₂ ⟩)
                                             ≅⟨ sym ass ⟩
                                             (π₁ ∙ ⟨ π₂ ∙ π₁ , π₂ ⟩)
                                               ∙ ⟨ ⟨ π₁ , π₁ ∙ π₂ ⟩ , π₂ ∙ π₂ ⟩ 
                                             ≅⟨ cong (λ x → x ∙ ⟨ ⟨ π₁ , π₁ ∙ π₂ ⟩ , π₂ ∙ π₂ ⟩)
                                                     law1 ⟩
                                             (π₂ ∙ π₁) ∙ ⟨ ⟨ π₁ , π₁ ∙ π₂ ⟩ , π₂ ∙ π₂ ⟩ 
                                             ≅⟨ ass ⟩
                                             π₂ ∙ (π₁ ∙ ⟨ ⟨ π₁ , π₁ ∙ π₂ ⟩ , π₂ ∙ π₂ ⟩ )
                                             ≅⟨ cong (λ x → π₂ ∙ x) law1 ⟩
                                             π₂ ∙ ⟨ π₁ , π₁ ∙ π₂ ⟩
                                             ≅⟨ law2 ⟩
                                             π₁ ∙ π₂ ∎)
                                             (proof
                                               π₂ ∙ (⟨ π₂ ∙ π₁ , π₂ ⟩
                                                     ∙ ⟨ ⟨ π₁ , π₁ ∙ π₂ ⟩ , π₂ ∙ π₂ ⟩)
                                               ≅⟨ sym ass ⟩
                                               (π₂ ∙ ⟨ π₂ ∙ π₁ , π₂ ⟩)
                                                 ∙ ⟨ ⟨ π₁ , π₁ ∙ π₂ ⟩ , π₂ ∙ π₂ ⟩ 
                                               ≅⟨ cong (λ x → x ∙ ⟨ ⟨ π₁ , π₁ ∙ π₂ ⟩ , π₂ ∙ π₂ ⟩)
                                                       law2 ⟩
                                               π₂ ∙ ⟨ ⟨ π₁ , π₁ ∙ π₂ ⟩ , π₂ ∙ π₂ ⟩
                                               ≅⟨ law2 ⟩
                                               π₂ ∙ π₂ ∎) ⟩
                                     ⟨ π₁ ∙ π₂ , π₂ ∙ π₂ ⟩
                                     ≅⟨ sym (law3 refl refl) ⟩
                                     π₂ ∎)) ⟩
                      ⟨ π₁ ∙ π₁ , ⟨ π₂ ∙ π₁ , π₂ ⟩ ⟩ ∙ ⟨ ⟨ π₁ , π₁ ∙ π₂ ⟩ , π₂ ∙ π₂ ⟩ ∎))
                 (sym (proof
                      iden
                      ≅⟨ law3 idr idr ⟩
                      ⟨ π₁ , π₂ ⟩
                      ≅⟨ sym ( law3 (proof
                                    π₁ ∙ (⟨ ⟨ π₁ , π₁ ∙ π₂ ⟩ , π₂ ∙ π₂ ⟩
                                            ∙ ⟨ π₁ ∙ π₁ , ⟨ π₂ ∙ π₁ , π₂ ⟩ ⟩)
                                    ≅⟨ sym ass ⟩
                                    (π₁ ∙ ⟨ ⟨ π₁ , π₁ ∙ π₂ ⟩ , π₂ ∙ π₂ ⟩)
                                    ∙ ⟨ π₁ ∙ π₁ , ⟨ π₂ ∙ π₁ , π₂ ⟩ ⟩
                                    ≅⟨ cong (λ x → x ∙ ⟨ π₁ ∙ π₁ , ⟨ π₂ ∙ π₁ , π₂ ⟩ ⟩)
                                            law1 ⟩
                                    ⟨ π₁ , π₁ ∙ π₂ ⟩ ∙ ⟨ π₁ ∙ π₁ , ⟨ π₂ ∙ π₁ , π₂ ⟩ ⟩
                                    ≅⟨ law3 (proof
                                            π₁ ∙ (⟨ π₁ , π₁ ∙ π₂ ⟩
                                                    ∙ ⟨ π₁ ∙ π₁ , ⟨ π₂ ∙ π₁ , π₂ ⟩ ⟩)
                                            ≅⟨ sym ass ⟩
                                            (π₁ ∙ ⟨ π₁ , π₁ ∙ π₂ ⟩)
                                              ∙ ⟨ π₁ ∙ π₁ , ⟨ π₂ ∙ π₁ , π₂ ⟩ ⟩
                                            ≅⟨ cong (λ x → x ∙ ⟨ π₁ ∙ π₁ , ⟨ π₂ ∙ π₁ , π₂ ⟩ ⟩)
                                                    law1 ⟩
                                            π₁ ∙ ⟨ π₁ ∙ π₁ , ⟨ π₂ ∙ π₁ , π₂ ⟩ ⟩
                                            ≅⟨ law1 ⟩
                                            π₁ ∙ π₁ ∎)
                                            (proof
                                            π₂ ∙ (⟨ π₁ , π₁ ∙ π₂ ⟩
                                                    ∙ ⟨ π₁ ∙ π₁ , ⟨ π₂ ∙ π₁ , π₂ ⟩ ⟩)
                                            ≅⟨ sym ass ⟩
                                            (π₂ ∙ ⟨ π₁ , π₁ ∙ π₂ ⟩)
                                              ∙ ⟨ π₁ ∙ π₁ , ⟨ π₂ ∙ π₁ , π₂ ⟩ ⟩
                                            ≅⟨ cong (λ x → x ∙ ⟨ π₁ ∙ π₁ , ⟨ π₂ ∙ π₁ , π₂ ⟩ ⟩)
                                                    law2 ⟩
                                            (π₁ ∙ π₂) ∙ ⟨ π₁ ∙ π₁ , ⟨ π₂ ∙ π₁ , π₂ ⟩ ⟩
                                            ≅⟨ ass ⟩
                                            π₁ ∙ (π₂ ∙ ⟨ π₁ ∙ π₁ , ⟨ π₂ ∙ π₁ , π₂ ⟩ ⟩)
                                            ≅⟨ cong (λ x → π₁ ∙ x) law2 ⟩
                                            π₁ ∙ ⟨ π₂ ∙ π₁ , π₂ ⟩
                                            ≅⟨ law1 ⟩
                                            π₂ ∙ π₁ ∎) ⟩
                                    ⟨ π₁ ∙ π₁ ,  π₂ ∙ π₁ ⟩
                                    ≅⟨ sym (law3 refl refl) ⟩
                                    π₁ ∎)
                                    (proof
                                      π₂ ∙ (⟨ ⟨ π₁ , π₁ ∙ π₂ ⟩ , π₂ ∙ π₂ ⟩
                                              ∙ ⟨ π₁ ∙ π₁ , ⟨ π₂ ∙ π₁ , π₂ ⟩ ⟩)
                                      ≅⟨ sym ass ⟩
                                      (π₂ ∙ ⟨ ⟨ π₁ , π₁ ∙ π₂ ⟩ , π₂ ∙ π₂ ⟩)
                                        ∙ ⟨ π₁ ∙ π₁ , ⟨ π₂ ∙ π₁ , π₂ ⟩ ⟩
                                      ≅⟨ cong (λ x → x ∙ ⟨ π₁ ∙ π₁ , ⟨ π₂ ∙ π₁ , π₂ ⟩ ⟩)
                                              law2 ⟩
                                      (π₂ ∙ π₂) ∙ ⟨ π₁ ∙ π₁ , ⟨ π₂ ∙ π₁ , π₂ ⟩ ⟩ 
                                      ≅⟨ ass ⟩
                                      π₂ ∙ (π₂ ∙ ⟨ π₁ ∙ π₁ , ⟨ π₂ ∙ π₁ , π₂ ⟩ ⟩)
                                      ≅⟨ cong (λ x → π₂ ∙ x) law2 ⟩
                                      π₂ ∙ ⟨ π₂ ∙ π₁ , π₂ ⟩
                                      ≅⟨ law2 ⟩
                                      π₂ ∎) ) ⟩
                      ⟨ ⟨ π₁ , π₁ ∙ π₂ ⟩ , π₂ ∙ π₂ ⟩ ∙ ⟨ π₁ ∙ π₁ , ⟨ π₂ ∙ π₁ , π₂ ⟩ ⟩ ∎))


  {- Definir el morfismo pair -}
  pair : ∀{A B C D}(f : Hom A B)(g : Hom C D)
       → Hom (A × C) (B × D)
  pair f g = ⟨ f ∙ π₁ , g ∙ π₂ ⟩

  -- Probar las siguientes propiedades de pair
  -- MODIFICADO
  idpair : ∀{X Y} → pair (iden {X}) (iden {Y}) ≅ iden {X × Y}
  idpair = sym (law3 (proof
                     π₁ ∙ iden
                     ≅⟨ idr ⟩
                     π₁
                     ≅⟨ sym idl ⟩
                     iden ∙ π₁ ∎)
                     (proof
                       π₂ ∙ iden
                       ≅⟨ idr ⟩
                       π₂
                       ≅⟨ sym idl ⟩
                       iden ∙  π₂ ∎))

  compdistrib : ∀{A B C D E F}
              → (f : Hom B C)(g : Hom A B)
              → (h : Hom E F)(i : Hom D E)
              → pair (f ∙ g) (h ∙ i) ≅ pair f h ∙ pair g i
  compdistrib f g h i = sym (law3 (proof
                                  π₁ ∙ (pair f h ∙ pair g i)
                                  ≅⟨ sym ass ⟩
                                  (π₁ ∙ pair f h) ∙ pair g i
                                  ≅⟨ cong (λ x → x ∙ pair g i) law1 ⟩
                                  (f ∙ π₁) ∙ pair g i
                                  ≅⟨ ass ⟩
                                  f ∙ (π₁ ∙ pair g i)
                                  ≅⟨ cong (λ x → f ∙ x) law1 ⟩
                                  f ∙ (g ∙ π₁) 
                                  ≅⟨ sym ass ⟩
                                  (f ∙ g) ∙ π₁ ∎)
                                  (proof
                                    π₂ ∙ (pair f h ∙ pair g i)
                                    ≅⟨ sym ass ⟩
                                    (π₂ ∙ pair f h) ∙ pair g i
                                    ≅⟨ cong (λ x → x ∙ pair g i) law2 ⟩
                                    (h ∙ π₂) ∙ pair g i
                                    ≅⟨ ass ⟩
                                    h ∙ (π₂ ∙ pair g i)
                                    ≅⟨ cong (λ x → h ∙ x) law2 ⟩
                                    h ∙ (i ∙ π₂)
                                    ≅⟨ sym ass ⟩
                                    (h ∙ i) ∙ π₂ ∎))

  open import Categories.ProductCat
  open import Functors

  -- Probar que el producto de objetos _×_, junto con pair
  -- forman un funtor C ×C C → C

  prodPairFun : Fun (C ×C C) C
  prodPairFun = functor (λ xy → fst xy × snd xy)
                        (λ fg → pair (fst fg) (snd fg))
                        idpair
                        (λ { {f = f₁ , f₂} {g₁ , g₂} → compdistrib f₁ g₁ f₂ g₂ })
  
--------------------------------------------------
