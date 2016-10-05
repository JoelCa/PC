open import Categories

module ProdFunCat where
  open import Library hiding (_×_)
  open import Functors
  open import Functors.Cat
  open import Construcciones
  open import Construcciones2
  open import Categories.Products
  open import Categories.Coproducts
  open import Naturals
  
  open Fun

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


  -- Ejercicios Extra
  funPro : ∀{a}{b}{c}{d}{C : Cat {a} {b}}{D : Cat {c} {d}} →
           Products D → Products (FunctorCat C D)
  funPro {C = C} {D} p =
    let open Products p
        open ProductMorphisms p using (pair ; idpair ; pairLema)
        open Cat C renaming (_∙_ to _∙C_ ; iden to idenC) hiding (ass)
        open Cat D renaming (_∙_ to _∙D_ ; iden to idenD)
        _**_ = _**_ p
    in prod (_**_)
            (λ {_} {_} → natural π₁ (sym law1))
            (λ {_} {_} → natural π₂ (sym law2))
            (λ {F} {G} {H} → λ { {natural α p₁} {natural β p₂} →
                                 natural (λ {_} →  ⟨ α , β ⟩)
                                         (λ {_} {_} {f} →
                                           proof
                                             HMap (F ** G) f ∙D ⟨ α , β ⟩
                                             ≅⟨ pairLema ⟩
                                             ⟨ HMap F f ∙D α , HMap G f ∙D β ⟩
                                             ≅⟨ cong₂ (λ x y → ⟨ x , y ⟩) p₁ p₂ ⟩
                                             ⟨ α ∙D HMap H f , β ∙D HMap H f ⟩
                                             ≅⟨ sym (law3 (proof
                                                          π₁ ∙D ⟨ α , β ⟩ ∙D HMap H f
                                                          ≅⟨ sym ass ⟩
                                                          (π₁ ∙D ⟨ α , β ⟩) ∙D HMap H f
                                                          ≅⟨ cong (λ x → x ∙D HMap H f) law1 ⟩
                                                          α ∙D HMap H f ∎)
                                                          (proof
                                                            π₂ ∙D ⟨ α , β ⟩ ∙D HMap H f
                                                            ≅⟨ sym ass ⟩
                                                            (π₂ ∙D ⟨ α , β ⟩) ∙D HMap H f
                                                            ≅⟨ cong (λ x → x ∙D HMap H f) law2 ⟩
                                                            β ∙D HMap H f ∎)) ⟩
                                             ⟨ α , β ⟩ ∙D HMap H f ∎) })
            (λ {_} {_} {_} {_} {_} → NatTEq (iext (λ _ → law1)) )
            (λ {_} {_} {_} {_} {_} → NatTEq (iext (λ _ → law2)))
            (λ { {f = natural α p₁} {natural β p₂} {natural γ p₃} x y →
               NatTEq (iext (λ c → law3 (NatTEqApp x c) (NatTEqApp y c)))})


  funCoPro : ∀{a}{b}{c}{d}{C : Cat {a} {b}}{D : Cat {c} {d}} →
             Coproducts D → Coproducts (FunctorCat C D)
  funCoPro {C = C} {D} cop =
    let proOp = CoproductProductDuality cop
        proFunCat = funPro {C = C Op} proOp
        open Products proFunCat
    in coproduct (λ F G → Fop← ((Fop→ F) × (Fop→ G)))
                 (λ {F} {G} → NatOp← (π₁ {Fop→ F} {Fop→ G}))
                 (λ {F} {G} → NatOp← (π₂ {Fop→ F} {Fop→ G}))
                 (λ {F} {G} {H} α β →
                    NatOp← (⟨_,_⟩ {Fop→ F} {Fop→ G} {Fop→ H}
                           (NatOp→ α) (NatOp→ β)))
                 (λ {F} {G} {H} {α} {β} →
                    NatTEq (iext (λ c → NatTEqApp (law1 {Fop→ F} {Fop→ G} {Fop→ H}
                                                        {NatOp→ α} {NatOp→ β}) c)))
                 (λ {F} {G} {H} {α} {β} →
                   NatTEq (iext (λ c → NatTEqApp (law2 {Fop→ F} {Fop→ G} {Fop→ H}
                                                        {NatOp→ α} {NatOp→ β}) c)))
                 (λ {F} {G} {H} {α} {β} {γ} x y →
                   NatTEq (iext (λ c → NatTEqApp (law3 {Fop→ F} {Fop→ G} {Fop→ H}
                                                       {NatOp→ α} {NatOp→ β} {NatOp→ γ}
                                                       (NatTEq (iext (λ a → NatTEqApp x a)))
                                                       (NatTEq (iext (λ a → NatTEqApp y a))))
                                                 c)))
