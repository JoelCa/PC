open import Categories

module Construcciones2 where

open import Library hiding (_×_ ; swap; _+_)

open import Categories.Products
open import Categories.Terminal
open import Categories.Iso
open import Categories.Initial
open import Categories.Coproducts
open import Construcciones

--------------------------------------------------

module SetsStructure {l : Level} where

 open import Categories.Sets

 {- Probar que la categoría Sets tiene objeto inicial y coproductos -}
 ZeroSetI : Initial Sets ⊥
 ZeroSetI = init ⊥-elim (λ { {x} {f} → ext (λ a → ⊥-elim a) })



 data _⊎₂_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : (x : A) → A ⊎₂ B
  inj₂ : (y : B) → A ⊎₂ B

 [_,_] : ∀ {a b c} {A : Set a} {B : Set b} {C : A ⊎₂ B → Set c} →
         ((x : A) → C (inj₁ x)) → ((x : B) → C (inj₂ x)) →
         ((x : A ⊎₂ B) → C x)
 [ f , g ] (inj₁ x) = f x
 [ f , g ] (inj₂ y) = g y

 SetsHasCoproductsI : ∀{l} → Coproducts (Sets {l})
 SetsHasCoproductsI = coproduct (λ x y → x ⊎₂ y)
                               inj₁
                               inj₂
                               (λ f g x →  [ f , g ] x)
                               refl
                               refl
                               (λ {_} {_} {_} {f} {g} {h} p₁ p₂ →
                                 ext (λ { (inj₁ x) → cong-app p₁ x ;
                                          (inj₂ x) → cong-app p₂ x }))

--------------------------------------------------
module InitialIso {a}{b}(C : Cat {a}{b}) where

 open Cat C
 open Initial

 {- el morfismo universal del objeto inicial a sí mismo es la identidad -}

 init-iden : (I : Obj){init : Initial C I}
           → i init {I} ≅ iden {I}
 init-iden I = λ {ini} → law ini


--------------------------------------------------
 {- Probar que un objeto terminal es inicial en la categoría dual y viceversa -}
 TerminalInitialDuality : {X : Obj} → Terminal C X → Initial (C Op) X
 TerminalInitialDuality = λ term → init (Terminal.t term ) (Terminal.law term)

 InitialTerminalDuality : {X : Obj} → Initial C X → Terminal (C Op) X
 InitialTerminalDuality = λ ini → term (i ini) (Initial.law ini)

--------------------------------------------------

 open TerminalIso
 
 {- Probar que dos objetos iniciales son necesariamente isomorfos *usando dualidad* -}
 InitialIso : (I I' : Obj)
            → (p : Initial C I)
            → (q : Initial C I')
            → Iso C (i p {I'})
 InitialIso I I' p q = let termCop = TerminalIso (C Op) I I' (InitialTerminalDuality p)
                                                             (InitialTerminalDuality q)
                       in iso (Iso.inv termCop) (Iso.linv termCop) (Iso.rinv termCop)

--------------------------------------------------------
-- Probar que los coproductos son productos en la categoría dual
ProductCoproductDuality : ∀{a}{b}{C : Cat {a}{b}}
                        → Products C
                        → Coproducts (C Op)
ProductCoproductDuality (prod _×_ π₁ π₂ ⟨_,_⟩ law1 law2 law3) =
  coproduct _×_ π₁ π₂ ⟨_,_⟩ law1 law2 law3

CoproductProductDuality : ∀{a}{b}{C : Cat {a}{b}}
                        → Coproducts C
                        → Products (C Op)
CoproductProductDuality (coproduct _+_ inl inr [_,_] law1 law2 law3) =
  prod _+_ inl inr [_,_] law1 law2 law3

--------------------------------------------------
module CoproductIso {a}{b}(C : Cat {a}{b})  where

  open Coproducts

  open Cat C

  open ProductIso (C Op) renaming (ProductIso to piso)

  {- Probar que los coproductos son únicos hasta un isomorfismo *usando dualidad* -}
  CoproductIso : ∀{A B}(X Y : Coproducts C) → Iso C ([_,_] X {A} {B} (inl Y) (inr Y))
  CoproductIso {A} {B} X Y = let isoCop = piso {A} {B} (CoproductProductDuality X)
                                                       (CoproductProductDuality Y)
                             in iso (Iso.inv isoCop) (Iso.linv isoCop) (Iso.rinv isoCop)

--------------------------------------------------

module CoproductMorphisms {a}{b}{C : Cat {a}{b}}{cp : Coproducts C} where

  open Cat C
  open Coproducts cp

  {- Definir el siguiente morfismo -}
  plus : ∀{A B C D}(f : Hom A B)(g : Hom C D) → Hom (A + C) (B + D)
  plus f g = [ inl ∙ f , inr ∙ g  ]


  {- Probar las siguentes propiedades -}

  idplus : ∀{A B} → plus (iden {A}) (iden {B}) ≅ iden {A + B}
  idplus = sym (law3 (proof iden ∙ inl
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

  idcomp :  ∀{A B C D E F}
         → (f : Hom B C)(g : Hom A B)
         → (h : Hom E F)(i : Hom D E)
         → plus (f ∙ g) (h ∙ i) ≅ plus f h ∙ plus g i
  idcomp  f g h i = sym (law3 (proof
                              (plus f h ∙ plus g i) ∙ inl
                              ≅⟨ ass ⟩
                              plus f h ∙ (plus g i ∙ inl)
                              ≅⟨ cong (λ x → plus f h ∙ x) law1 ⟩
                              plus f h ∙ (inl ∙ g)
                              ≅⟨ sym ass ⟩
                              (plus f h ∙ inl) ∙ g
                              ≅⟨ cong (λ x → x ∙ g) law1 ⟩
                              (inl ∙ f) ∙ g
                              ≅⟨ ass ⟩
                              inl ∙ (f ∙ g) ∎)
                              (proof
                                (plus f h ∙ plus g i) ∙ inr
                                ≅⟨ ass ⟩
                                plus f h ∙ (plus g i ∙ inr)
                                ≅⟨ cong (λ x → plus f h ∙ x) law2 ⟩
                                plus f h ∙ (inr ∙ i)
                                ≅⟨ sym ass ⟩
                                (plus f h ∙ inr) ∙ i
                                ≅⟨ cong (λ x → x ∙ i) law2 ⟩
                                (inr ∙ h) ∙ i
                                ≅⟨ ass ⟩
                                inr ∙ (h ∙ i) ∎))


   {- Probar que _+_ junto con plus definen unFunctor C ×C C → C -}
  open import Categories.ProductCat
  open import Functors

  coprodPlusFun : Fun (C ×C C) C
  coprodPlusFun = functor (λ xy → fst xy + snd xy)
                          (λ fg → plus (fst fg) (snd fg) )
                          idplus
                          (λ { {f = f₁ , f₂} {g₁ , g₂} → idcomp f₁ g₁ f₂ g₂ })


module Intercambio {a}{b}{C : Cat {a}{b}}{cp : Coproducts C}{p : Products C} where

  open Cat C
  open Coproducts cp
  open Products p renaming (law1 to lawp1 ; law2 to lawp2 ; law3 to lawp3)


   {- intercambio entre poducto y coproducto -}

  intercambio : ∀{A B C D}
         → (f : Hom A C)(g : Hom B C)
         → (h : Hom A D)(k : Hom B D)
         → ⟨ [ f , g ] , [ h , k ] ⟩ ≅ [ ⟨ f , h ⟩ , ⟨ g , k ⟩ ]
  intercambio f g h i = law3 (lawp3 (proof
                                    π₁ ∙ ⟨ [ f , g ] , [ h , i ] ⟩ ∙ inl
                                    ≅⟨ sym ass ⟩
                                    (π₁ ∙ ⟨ [ f , g ] , [ h , i ] ⟩) ∙ inl
                                    ≅⟨ cong (λ x → x ∙ inl) lawp1 ⟩
                                    [ f , g ] ∙ inl
                                    ≅⟨ law1 ⟩
                                    f ∎)
                                    (proof
                                      π₂ ∙ ⟨ [ f , g ] , [ h , i ] ⟩ ∙ inl
                                      ≅⟨ sym ass ⟩
                                      (π₂ ∙ ⟨ [ f , g ] , [ h , i ] ⟩) ∙ inl
                                      ≅⟨ cong (λ x → x ∙ inl) lawp2 ⟩
                                      [ h , i ] ∙ inl
                                      ≅⟨ law1 ⟩
                                      h ∎))
                             (lawp3 (proof
                                    π₁ ∙ ⟨ [ f , g ] , [ h , i ] ⟩ ∙ inr
                                    ≅⟨ sym ass ⟩
                                    (π₁ ∙ ⟨ [ f , g ] , [ h , i ] ⟩) ∙ inr
                                    ≅⟨ cong (λ x → x ∙ inr) lawp1 ⟩
                                    [ f , g ] ∙ inr
                                    ≅⟨ law2 ⟩
                                    g ∎)
                                    (proof
                                      π₂ ∙ ⟨ [ f , g ] , [ h , i ] ⟩ ∙ inr
                                      ≅⟨ sym ass ⟩
                                      (π₂ ∙ ⟨ [ f , g ] , [ h , i ] ⟩) ∙ inr
                                      ≅⟨ cong (λ x → x ∙ inr) lawp2 ⟩
                                      [ h , i ] ∙ inr
                                      ≅⟨ law2 ⟩
                                      i ∎))
