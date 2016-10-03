
open import Categories
open import Categories.Coproducts


module Categories.Coproducts.Properties {l m}{C : Cat {l}{m}}(c : Coproducts C) where

open import Library hiding (_+_)
open Cat C
open Coproducts c

copair : ∀{X Y Z W}(f : Hom X Z)(g : Hom Y W) → Hom (X + Y) (Z + W)
copair f g = [ inl ∙ f , inr ∙ g ]

iden-cop : ∀{A B} →  copair (iden {A}) (iden {B}) ≅ iden {A + B}
iden-cop = sym (law3 (proof iden ∙ inl
                     ≅⟨ idl ⟩
                     inl
                     ≅⟨ sym idr ⟩
                     inl ∙ iden ∎)
                     (proof
                       iden ∙ inr
                       ≅⟨ idl ⟩
                       inr
                       ≅⟨ sym idr ⟩
                       inr ∙ iden ∎))


comp-cop : ∀{A B C A' B' C'}{f : Hom B C}{g : Hom A B}{h : Hom B' C'}{i : Hom A' B'}
         → copair (f ∙ g) (h ∙ i) ≅ copair f h ∙ copair g i
comp-cop {f = f} {g} {h} {i} = sym (law3 (proof
                                         (copair f h ∙ copair g i) ∙ inl
                                         ≅⟨ ass ⟩
                                         copair f h ∙ (copair g i ∙ inl)
                                         ≅⟨ cong (λ x → copair f h ∙ x) law1 ⟩
                                         copair f h ∙ (inl ∙ g)
                                         ≅⟨ sym ass ⟩
                                         (copair f h ∙ inl) ∙ g
                                         ≅⟨ cong (λ x → x ∙ g) law1 ⟩
                                         (inl ∙ f) ∙ g
                                         ≅⟨ ass ⟩
                                         inl ∙ (f ∙ g) ∎)
                                         (proof
                                           (copair f h ∙ copair g i) ∙ inr
                                           ≅⟨ ass ⟩
                                           copair f h ∙ (copair g i ∙ inr)
                                           ≅⟨ cong (λ x → copair f h ∙ x) law2 ⟩
                                           copair f h ∙ (inr ∙ i)
                                           ≅⟨ sym ass ⟩
                                           (copair f h ∙ inr) ∙ i
                                           ≅⟨ cong (λ x → x ∙ i) law2 ⟩
                                           (inr ∙ h) ∙ i
                                           ≅⟨ ass ⟩
                                           inr ∙ (h ∙ i) ∎))


inl-cop : ∀{A B C}{f : Hom C A}{g : Hom C B} → copair f g ∙ inl ≅ inl {A} {B} ∙ f
inl-cop = law1

inr-cop : ∀{A B C}{f : Hom C A}{g : Hom C B} → copair f g ∙ inr ≅ inr {A} {B} ∙ g
inr-cop = law2

fusion-cop : ∀{A B C D E}{f : Hom A B}{g : Hom C D}{h : Hom B E}{i : Hom D E} 
          → [ h , i ] ∙ (copair f g) ≅ [ h ∙ f , i ∙ g ]
fusion-cop {f = f} {g} {h} {i} = law3 (proof 
                                      ([ h , i ] ∙ copair f g) ∙ inl 
                                      ≅⟨ ass ⟩ 
                                      [ h , i ] ∙ (copair f g ∙ inl) 
                                      ≅⟨ cong (λ x → [ h , i ] ∙ x) law1 ⟩
                                      [ h , i ] ∙ (inl ∙ f) 
                                      ≅⟨ sym ass ⟩
                                      ([ h , i ] ∙ inl) ∙ f 
                                      ≅⟨ cong (λ x → x ∙ f) law1 ⟩
                                      h ∙ f ∎) 
                                      (proof 
                                        ([ h , i ] ∙ copair f g) ∙ inr 
                                        ≅⟨ ass ⟩
                                        [ h , i ] ∙ (copair f g ∙ inr) 
                                        ≅⟨ cong (λ x → [ h , i ] ∙ x) law2 ⟩ 
                                        [ h , i ] ∙ (inr ∙ g) 
                                        ≅⟨ sym ass ⟩ 
                                        ([ h , i ] ∙ inr) ∙ g 
                                        ≅⟨ cong (λ x → x ∙ g) law2 ⟩
                                        i ∙ g ∎)