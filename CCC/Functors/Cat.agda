module Functors.Cat where

open import Library hiding (_×_ ; _+_)
open import Categories
open import Functors
open import Naturals

idlNat : ∀{a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}{F G : Fun C D}
         {α : NatT F G} → compVNat idNat α ≅ α
idlNat {D = D} = NatTEq (Cat.idl D)

idrNat : ∀{a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}{F G : Fun C D}
         {α : NatT F G} → compVNat α idNat ≅ α
idrNat {D = D} = NatTEq (Cat.idr D)
 
assNat : ∀{a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}{E F G H : Fun C D}
         {α : NatT G H}{β : NatT F G}{η : NatT E F} → 
         compVNat (compVNat α β) η ≅ compVNat α (compVNat β η)
assNat {D = D} = NatTEq (Cat.ass D)

FunctorCat : ∀{a b c d} → Cat {a}{b} → Cat {c}{d} → Cat
FunctorCat C D = record{
  Obj  = Fun C D;
  Hom  = NatT;
  iden = idNat;
  _∙_  = compVNat;
  idl  = idlNat;
  idr  = idrNat;
  ass  = λ{_}{_}{_}{_}{α}{β}{η} → assNat {α = α}{β}{η}}


open import Categories.Products
open import Functors.Product
open Fun
open import Categories.CAT renaming (pair to pairCAT)

{- Functor categories have point-wise products -}
FunctorCatProducts : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}
                   → (p : Products D) → Products (FunctorCat C D)
FunctorCatProducts {C = C}{D} p = let open Cat D
                                      open Products p
                                      open ProductMorphisms p
                        in
                        prod (_×F_ p)
                             (natural π₁ (sym law1))
                             (natural π₂ (sym law2))
                             (λ {F} {G} {H} f g → natural (⟨ NatT.cmp f , NatT.cmp g ⟩) (λ {X}{Y}{h} → proof
                                pair (HMap F h) (HMap G h) ∙ ⟨ NatT.cmp f , NatT.cmp g ⟩
                              ≅⟨ law3 (trans (sym ass) (trans (cong₂ _∙_ law1 refl) (trans ass (cong₂ _∙_ refl law1))))
                                      (trans (sym ass) (trans (cong₂ _∙_ law2 refl) (trans ass (cong₂ _∙_ refl law2)))) ⟩
                                ⟨ HMap F h ∙ NatT.cmp f , HMap G h ∙ NatT.cmp g ⟩
                              ≅⟨ sym (law3 (trans (sym ass) (trans (cong₂ _∙_ law1 refl) (sym (NatT.nat f))))
                                           (trans (sym ass) (trans (cong₂ _∙_ law2 refl) (sym (NatT.nat g))))) ⟩
                                ⟨ NatT.cmp f , NatT.cmp g ⟩ ∙ HMap H h
                              ∎))
                             (NatTEq law1)
                             (NatTEq law2)
                             (λ {F}{G}{H}{f} {g} p1 p2 → NatTEq {_} {_} {_} {_} {C} {D} {H} (λ {X} →
                                                         law3 (cong {_} {_} { NatT H F }
                                                                            { λ _ → Hom (OMap H X) (OMap F X) } (λ τ → NatT.cmp τ {X}) p1)
                                                              (cong {_} {_} { NatT H G } { λ _ → Hom (OMap H X) (OMap G X) } (λ τ → NatT.cmp τ {X}) p2)))

open import Categories.Coproducts
open import Categories.Coproducts.Properties 

FunctorCatCoproducts : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}
                   → (c : Coproducts D) → Coproducts (FunctorCat C D)
FunctorCatCoproducts {C = C}{D} c = let open Cat D
                                        open Coproducts c
             in coproduct (λ F G → functor (λ X →  OMap F X + OMap G X)
                                              (λ f → copair (HMap F f) (HMap G f))
                                              (proof
                                               copair (HMap F (Cat.iden C)) (HMap G (Cat.iden C))
                                               ≅⟨ cong₂ copair (fid F) (fid G) ⟩
                                                copair iden iden
                                               ≅⟨ iden-cop c ⟩
                                               iden ∎)
                                              (λ {_}{_}{_}{f}{g} → proof
                                                 copair (HMap F ((C Cat.∙ f) g)) (HMap G ((C Cat.∙ f) g))
                                                ≅⟨ cong₂ copair (fcomp F) (fcomp G) ⟩
                                                 copair (HMap F f ∙ HMap F g) (HMap G f ∙ HMap G g)
                                                ≅⟨ comp-cop c  ⟩
                                                 copair (HMap F f) (HMap G f) ∙ copair (HMap F g) (HMap G g)
                                                ∎))
                             (natural inl law1)
                             (natural inr law2)
                             (λ {F} {G} {H} f g → natural ([ NatT.cmp f , NatT.cmp g ]) (λ {X}{Y}{h} → proof
                                 HMap H h ∙ [ NatT.cmp f , NatT.cmp g ]
                              ≅⟨ fusion c ⟩
                                [ HMap H h ∙ NatT.cmp f , HMap H h ∙ NatT.cmp g ]
                              ≅⟨ cong₂ [_,_] (NatT.nat f) (NatT.nat g) ⟩
                                [ NatT.cmp f ∙ HMap F h , NatT.cmp g ∙ HMap G h ]
                              ≅⟨ sym (fusion-cop c) ⟩
                                [ NatT.cmp f , NatT.cmp g ] ∙ copair (HMap F h) (HMap G h)
                              ∎))
                             (NatTEq law1)
                             (NatTEq law2)
                             (λ {F}{G}{H}{f} {g} p1 p2 → NatTEq (λ {X} → law3 (cong {_}{_}{_}{λ _ → Hom (OMap F X) (OMap H X)} (λ τ → NatT.cmp τ {X}) p1 )
                                                                               ((cong {_}{_}{_}{λ _ → Hom (OMap G X) (OMap H X)} (λ τ → NatT.cmp τ {X}) p2 ))))
