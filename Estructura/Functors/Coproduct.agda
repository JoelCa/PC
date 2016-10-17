
open import Categories
open import Categories.Coproducts

module Functors.Coproduct {a b}{C : Cat {a}{b}}(cop : Coproducts C) where

open import Library hiding (_+_)

open import Functors

open Cat C
open Coproducts cop
open import Categories.Coproducts.Properties cop
open Fun

_+F_ : ∀{c d}{D : Cat {c} {d}} → Fun D C → Fun D C → Fun D C
_+F_ {D = D} F G = functor (λ X →  OMap F X + OMap G X)
                (λ f → copair (HMap F f) (HMap G f))
                (proof
                  copair (HMap F (Cat.iden D)) (HMap G (Cat.iden D))
                ≅⟨ cong₂ copair (fid F) (fid G)  ⟩
                  copair iden iden
                ≅⟨ iden-cop ⟩
                  iden ∎)
                (λ {X Y Z f g} → proof
                  copair (HMap F (Cat._∙_ D f g)) (HMap G (Cat._∙_ D f g))
                  ≅⟨ cong₂ copair (fcomp F) (fcomp G) ⟩
                  copair (HMap F f ∙ HMap F g) (HMap G f ∙ HMap G g)
                  ≅⟨ cong₂ [_,_] (sym ass) (sym ass) ⟩
                   [ (inl ∙ HMap F f) ∙ HMap F g , (inr ∙ HMap G f) ∙ HMap G g ]
                  ≅⟨ sym fusion-cop ⟩
                  copair (HMap F f) (HMap G f) ∙ copair (HMap F g) (HMap G g) ∎)

open import Naturals

copairF : ∀{c d}{D : Cat {c} {d}}{F G H K} →
          (NatT {C = D} F H) → (NatT G K) → NatT (F +F G) (H +F K)
copairF {F = F} {G} {H} {K} (natural α natα) (natural β natβ) =
                         natural (copair α β)
                                 (λ { X Y f } → proof
                                     HMap (H +F K) f ∙ copair α β
                                   ≅⟨ fusion-cop ⟩
                                     [ (inl ∙ HMap H f) ∙ α , (inr ∙ HMap K f) ∙ β ]
                                   ≅⟨ cong₂ [_,_] ass ass ⟩
                                    copair (HMap H f ∙ α) (HMap K f ∙ β)
                                   ≅⟨ cong₂ copair natα natβ ⟩
                                    copair (α ∙ HMap F f) (β ∙ HMap G f)
                                   ≅⟨ comp-cop ⟩
                                    copair α β ∙ HMap (F +F G) f
                                   ∎)
