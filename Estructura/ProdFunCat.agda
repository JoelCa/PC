open import Categories

module ProdFunCat where
  open import Library hiding (_×_)
  open import Functors
  open import Functors.Cat
  open import Construcciones
  open import Categories.Products
  open import Categories.Coproducts
  open import Naturals
  
  open Fun
  --open Cat

  _**_ : ∀{a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}} → 
         Products D → Fun C D → Fun C D → Fun C D
  _**_ {C = C} {D} p F G =
    let open Products p
        open Cat C renaming (_∙_ to _∙C_ ; iden to idenC) hiding (ass)
        open Cat D renaming (_∙_ to _∙D_ ; iden to idenD)
        open ProductMorphisms p using (pair ; idpair)
    in functor (λ x → OMap F x × OMap G x)
               (λ f → pair (HMap F f) (HMap G f))
               (λ {_} → proof pair (HMap F idenC) (HMap G idenC)
                              ≅⟨ cong₂ (λ x y → pair x y) (fid F) (fid G) ⟩ 
                              pair idenD idenD 
                              ≅⟨ idpair ⟩ 
                              idenD ∎)
               (λ {_} {_} {_} {g} {f} →
                  sym (law3 (proof
                            π₁ ∙D (pair (HMap F g) (HMap G g) ∙D pair (HMap F f) (HMap G f))
                            ≅⟨ sym ass ⟩
                            (π₁ ∙D pair (HMap F g) (HMap G g)) ∙D pair (HMap F f) (HMap G f)
                            ≅⟨ cong (λ x → x ∙D pair (HMap F f) (HMap G f)) law1 ⟩
                            (HMap F g ∙D π₁) ∙D pair (HMap F f) (HMap G f)
                            ≅⟨ ass ⟩
                            HMap F g ∙D (π₁ ∙D pair (HMap F f) (HMap G f))
                            ≅⟨ cong (λ x → HMap F g ∙D x) law1 ⟩
                            HMap F g ∙D (HMap F f ∙D π₁)
                            ≅⟨ sym ass ⟩
                            (HMap F g ∙D HMap F f) ∙D π₁
                            ≅⟨ cong (λ x → x ∙D π₁) (sym (fcomp F)) ⟩
                            HMap F (g ∙C f) ∙D π₁ ∎)
                            (proof
                              π₂ ∙D (pair (HMap F g) (HMap G g) ∙D pair (HMap F f) (HMap G f))
                              ≅⟨ sym ass ⟩
                              (π₂ ∙D pair (HMap F g) (HMap G g)) ∙D pair (HMap F f) (HMap G f)
                              ≅⟨ cong (λ x → x ∙D pair (HMap F f) (HMap G f)) law2 ⟩
                              (HMap G g ∙D π₂) ∙D pair (HMap F f) (HMap G f)
                              ≅⟨ ass ⟩
                              HMap G g ∙D (π₂ ∙D pair (HMap F f) (HMap G f))
                              ≅⟨ cong (λ x → HMap G g ∙D x) law2 ⟩
                              HMap G g ∙D (HMap G f ∙D π₂)
                              ≅⟨ sym ass ⟩
                              (HMap G g ∙D HMap G f) ∙D π₂
                              ≅⟨ cong (λ x → x ∙D π₂) (sym (fcomp G)) ⟩
                              HMap G (g ∙C f) ∙D π₂ ∎)))


  funPro : ∀{a}{b}{c}{d}{C : Cat {a} {b}}{D : Cat {c} {d}} →
           Products D → Products (FunctorCat C D)
  funPro {C = C} {D} p =
    let open Products p
        open ProductMorphisms p using (pair ; idpair)
        open Cat C renaming (_∙_ to _∙C_ ; iden to idenC)
        open Cat D renaming (_∙_ to _∙D_ ; iden to idenD)                 
    in prod (_**_ p)
            (λ {_} {_} → natural π₁ (sym law1))
            (λ {_} {_} → natural π₂ (sym law2))
            {!!}
            {!!}
            {!!}
            {!!}

  funCoPro : ∀{a}{b}{c}{d}{C : Cat {a} {b}}{D : Cat {c} {d}} →
             Coproducts D → Coproducts (FunctorCat C D)
  funCoPro = {!!}
