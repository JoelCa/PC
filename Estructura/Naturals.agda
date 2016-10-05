module Naturals where

open import Library
open import Categories
open import Functors

open Fun

record NatT {a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}(F G : Fun C D) : Set (a ⊔ b ⊔ d) where
  constructor natural
  open Cat
  field cmp : ∀ {X} → Hom D (OMap F X) (OMap G X)
        nat : ∀{X Y}{f : Hom C X Y} → 
              _∙_ D (HMap G f) cmp ≅ _∙_ D cmp (HMap F f)

-- Dos transformaciones naturales son iguales si sus componentes son iguales.
NatTEq : ∀{a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}{F G : Fun C D}
         {α β : NatT F G} → 
         (λ {X} → NatT.cmp α {X}) ≅ (λ {X} → NatT.cmp β {X}) → 
         α ≅ β
NatTEq {α = natural cmp _} {natural .cmp _} refl =
  cong (natural cmp) (iext λ _ → iext λ _ → iext λ _ → ir _ _)

-- NatTEq2 se puede usar cuando los funtores intervinientes no son definicionalmente iguales
NatTEq2 : ∀ {a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}{F G F' G' : Fun C D}
            {α : NatT F G}{β : NatT F' G'}
          → F ≅ F' → G ≅ G'  
          → (λ {X} → NatT.cmp α {X}) ≅ (λ {X} → NatT.cmp β {X})
          → α ≅ β
NatTEq2 {α = natural cmp _} {natural .cmp _} refl refl refl =
  cong (natural cmp) (iext λ _ → iext λ _ → iext λ _ → ir _ _)


--AGREGADOS por mi
NatOp← : ∀{a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}
        {F G : Fun (C Op) (D Op)} → NatT F G → NatT (Fop← G) (Fop← F)
NatOp← {F = F} {G} (natural cmp nat) = natural cmp (sym nat)

NatOp→ : ∀{a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}
        {F G : Fun C D} → NatT F G → NatT (Fop→ G) (Fop→ F)
NatOp→ {F = F} {G} (natural cmp nat) = natural cmp (sym nat)

NatTEqApp : ∀{a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}{F G : Fun C D}
            {α β : NatT F G} →
            α ≅ β → (X : Cat.Obj C) →
            NatT.cmp α {X} ≅ NatT.cmp β {X}
NatTEqApp refl x = refl

--------------------------------------------------
-- la identidad es una transformación natural
idNat : ∀{a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}{F : Fun C D} → NatT F F
idNat {D = D}{F} = let open Cat D in
                   natural iden (λ {_} {_} {f} →
                                   proof
                                   HMap F f ∙ iden
                                   ≅⟨ idr ⟩
                                   HMap F f
                                   ≅⟨ sym idl ⟩
                                   iden ∙ HMap F f ∎)

-- Composición (vertical) de transformaciones naturales
compVNat : ∀{a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}{F G H : Fun C D} → 
          NatT G H → NatT F G → NatT F H
compVNat {D = D}{F}{G}{H} (natural β p₂) (natural α p₁) = let open Cat D; open NatT in
                                                          natural (β ∙ α)
                                                          (λ {_} {_} {f} →
                                                            proof
                                                            HMap H f ∙ (β ∙ α)
                                                            ≅⟨ sym ass ⟩
                                                            (HMap H f ∙ β) ∙ α
                                                            ≅⟨ cong (λ x → x ∙ α) p₂ ⟩
                                                            (β ∙ HMap G f) ∙ α
                                                            ≅⟨ ass ⟩
                                                            β ∙ (HMap G f ∙ α)
                                                            ≅⟨ cong (λ x → β ∙ x) p₁ ⟩
                                                            β ∙ (α ∙ HMap F f)
                                                            ≅⟨ sym ass ⟩
                                                            (β ∙ α) ∙ HMap F f ∎)

-- --------------------------------------------------
-- {- Categorías de funtores
--  Dadas dos categorías C y D, los objetos son los funtores : C → D,
--  y los morfismos son las transformaciones naturales entre ellos.
-- -}
-- FunctorCat : ∀{a b c d} → Cat {a}{b} → Cat {c}{d} → Cat
-- FunctorCat C D = let open Cat D in
--                  record{
--                  Obj  = Fun C D;
--                  Hom  = NatT;
--                  iden = idNat;
--                  _∙_  = compVNat;
--                  idl  = NatTEq (iext (λ x → idl));
--                  idr  = NatTEq (iext (λ x → idr));
--                  ass  = NatTEq (iext (λ x → ass))}

--------------------------------------------------
-- Algunos ejemplos de transformaciones naturales

module Ejemplos where

 open import Categories.Sets
 open import Functors.List
 open import Functors.Maybe
 open import Functors.Constant
 open import Data.Nat
 open import Data.List.Base renaming (map to mapList)
 open import Data.Maybe.Base renaming (map to mapMaybe)

 {- reverse es una transformación natural -}

 open Cat (Sets {lzero})

 --
 lemaMapFoldl : ∀ {a} {A : Set a} {B : Set a} →
                  {f : A → B} {c : ∀ {X} →  List X → X → List X} {xs : List A} →
                  (∀ {n} {x} → mapList f (c n x) ≅ c (mapList f n) (f x)) →
                  (∀ {n} → mapList f (foldl c n xs) ≅ foldl c (mapList f n) (mapList f xs))
 lemaMapFoldl {f = f} {c} {[]} h = refl
 lemaMapFoldl {f = f} {c} {(x ∷ xs)} h = λ {n} → proof
                                                 mapList f (foldl c (c n x) xs)
                                                 ≅⟨ lemaMapFoldl {xs = xs} h ⟩
                                                 foldl c (mapList f (c n x)) (mapList f xs)
                                                 ≅⟨ cong (λ x₁ → foldl c x₁ (mapList f xs)) h ⟩
                                                 foldl c (c (mapList f n) (f x)) (mapList f xs) ∎

 lemaRev : {A B : Set} {f : A → B} {xs : List A} →
              (mapList f) (reverse xs) ≅ reverse (mapList f xs)
 lemaRev {f = f} {xs} = lemaMapFoldl {f = f} {xs = xs} refl

 revNat : NatT ListF ListF
 revNat = natural reverse (λ {_} {_} {f} →
                             ext (λ xs → lemaRev {f = f} {xs}))

--
 distMap++ : ∀ {a} {b} {A : Set a} {B : Set b} {xs ys : List A} {f : A → B}
             → mapList f (xs ++ ys) ≅ mapList f xs ++ mapList f ys
 distMap++ {xs = []} = refl
 distMap++ {xs = x ∷ xs} = λ {ys} {f} → proof 
                                       f x ∷ mapList f (xs ++ ys) 
                                       ≅⟨ cong (λ x₁ → f x ∷ x₁) (distMap++ {xs = xs} {ys} {f}) ⟩ 
                                       f x ∷ mapList f xs ++ mapList f ys ∎ 

 lemaCon : ∀ {a} {b} {A : Set a} {B : Set b} {f : A → B} {xs : List (List A)} →
           mapList f (concat xs) ≅ concat (mapList (mapList f) xs)
 lemaCon {xs = []} = refl
 lemaCon {f = f} {xs ∷ xss} = proof
                              mapList f (xs ++ (concat xss)) 
                              ≅⟨ distMap++ {xs = xs} {concat xss} {f} ⟩ 
                              (mapList f xs) ++ (mapList f (concat xss))  
                              ≅⟨ cong (λ x → (mapList f xs) ++ x) (lemaCon {xs = xss}) ⟩ 
                              (mapList f xs) ++ concat (mapList (mapList f) xss) ∎

 concatNat : NatT (ListF ○ ListF) ListF
 concatNat = natural concat (λ {_} {_} {f} → ext (λ xss → lemaCon {f = f} {xs = xss}))

 --

 lemaLenMap : ∀ {A B : Set}{f : A → B} {xs : List A} → length (mapList f xs) ≅ length xs
 lemaLenMap {xs = []} = refl
 lemaLenMap {f = f} {xs = x ∷ xs} = proof
                            1 + length (mapList f xs) 
                            ≅⟨ cong (λ x₁ → 1 + x₁) (lemaLenMap {xs = xs}) ⟩ 
                            1 + length xs ∎

 lengthNat : NatT ListF (K ℕ)
 lengthNat = natural length (λ {_} {_} {f} → ext (λ xs → proof
                                                          length xs
                                                          ≅⟨ sym (lemaLenMap {f = f} {xs}) ⟩
                                                          length (mapList f xs) ∎))
 --
 safeHead : {A : Set} → List A → Maybe A
 safeHead [] = nothing
 safeHead (x ∷ xs) = just x

 lemaSafeH : ∀ {A B : Set}{f : A → B} {xs : List A} →
             mapMaybe f (safeHead xs) ≅ safeHead (mapList f xs)
 lemaSafeH {xs = []} = refl
 lemaSafeH {xs = x ∷ xs} = refl

 headNat : NatT ListF MaybeF
 headNat = natural safeHead ((λ {_} {_} {f} → ext (λ xs → lemaSafeH {xs = xs})))

--------------------------------------------------
-- Natural isomorphism
{- Un isomorfismo natural es una transformación natural tal que
   cada componente es un isomorfismo. -}
open import Categories.Iso

record NatIso {a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}
             {F G : Fun C D}(η : NatT F G)  : Set (a ⊔ d) where
  constructor natiso
  field cmpIso : ∀{X} -> Iso D (NatT.cmp η {X})


--------------------------------------------------
-- composición con funtor (a izquierda y a derecha)

compFNat : ∀{a b c d e f}{C : Cat {a} {b}}{D : Cat {c} {d}}{E : Cat {e} {f}}
            {F G : Fun C D}
         → (J : Fun D E)
         → (η : NatT F G) → NatT (J ○ F) (J ○ G)
compFNat {D = D} {E} {F} {G} J (natural η p) =
               let 
                   open Cat D renaming (_∙_ to _∙D_)
                   open Cat E renaming (_∙_ to _∙E_)
               in
               natural (HMap J η)
                       (λ {_} {_} {f} →
                         (proof
                         HMap J (HMap G f) ∙E HMap J η
                         ≅⟨ sym (fcomp J) ⟩ 
                         HMap J (HMap G f ∙D η)
                         ≅⟨ cong (λ x → HMap J x) p  ⟩ 
                         HMap J (η ∙D HMap F f)
                         ≅⟨ fcomp J ⟩
                         HMap J η ∙E  HMap J (HMap F f) ∎ ))

compNatF :  ∀{a b c d e f}{C : Cat {a} {b}}{D : Cat {c} {d}}{E : Cat {e} {f}}
            {J K : Fun D E}
         → (η : NatT J K)
         → (F : Fun C D)
         → NatT (J ○ F) (K ○ F)
compNatF {C = C} {D} {E} {J} {K} η F =
               let open NatT η
                   open Cat D renaming (_∙_ to _∙D_)
                   open Cat E renaming (_∙_ to _∙E_)
               in natural (λ {x} → cmp {OMap F x})
                          nat

--------------------------------------------------
-- Composición horizontal
compHNat : ∀{a b c d e f}{C : Cat {a} {b}}{D : Cat {c} {d}}{E : Cat {e} {f}}
            {F G : Fun C D}{J K : Fun D E}
            (η : NatT F G)(ε : NatT J K)
            → NatT (J ○ F) (K ○ G)
compHNat {D = D} {E} {F} {G} {J} {K} (natural η p₁) (natural ε p₂) =
  let
    open Cat D renaming (_∙_ to _∙D_)
    open Cat E renaming (_∙_ to _∙E_)
  in
  natural (λ {x} → ε {OMap G x} ∙E HMap J (η {x}))
          (λ {_} {_} {f} →
            proof
              HMap K (HMap G f) ∙E (ε ∙E HMap J η)
              ≅⟨ sym (cong (λ x →  HMap K (HMap G f) ∙E x) (p₂ {f = η})) ⟩
              HMap K (HMap G f) ∙E (HMap K η ∙E ε)
              ≅⟨ sym (Cat.ass E) ⟩
              (HMap K (HMap G f) ∙E (HMap K η)) ∙E ε
              ≅⟨ cong (λ x → x ∙E ε) (sym (fcomp K)) ⟩
              HMap K (HMap G f ∙D η) ∙E ε
              ≅⟨ cong (λ x → HMap K x ∙E ε) p₁ ⟩
              HMap K (η ∙D HMap F f) ∙E ε
              ≅⟨ cong (λ x → x ∙E ε) (fcomp K) ⟩
              (HMap K η ∙E HMap K (HMap F f)) ∙E ε
              ≅⟨ Cat.ass E ⟩
              HMap K η ∙E (HMap K (HMap F f) ∙E ε)
              ≅⟨ cong (λ x → HMap K η ∙E x) p₂ ⟩
              HMap K η ∙E (ε ∙E HMap J (HMap F f)) 
              ≅⟨ sym (Cat.ass E) ⟩
              (HMap K η ∙E ε) ∙E HMap J (HMap F f)              
              ≅⟨ cong (λ x → x ∙E HMap J (HMap F f) ) p₂ ⟩
              (ε ∙E HMap J η) ∙E HMap J (HMap F f)
              ∎)


-- La composición horizontal es asociativa
compHNat-assoc : ∀{a1 b1 a2 b2 a3 b3 a4 b4}
                    {C1 : Cat {a1} {b1}}{C2 : Cat {a2} {b2}}
                    {C3 : Cat {a3} {b3}}{C4 : Cat {a4} {b4}}
                    {F G : Fun C1 C2}{J K : Fun C2 C3}{L M : Fun C3 C4} 
                 →  (η1 : NatT F G)(η2 : NatT J K)(η3 : NatT L M)
                 →  compHNat (compHNat η1 η2) η3 ≅ compHNat η1 (compHNat η2 η3)
compHNat-assoc {C3 = C3}{C4 = C4}{J = J}{L = L}
               (natural cmp1 _) (natural cmp2 _) (natural cmp3 _) =
                   let   _∙4_ = Cat._∙_ C4
                         _∙3_ = Cat._∙_ C3                         
                   in
                   NatTEq2 (Functor-Eq refl refl) (Functor-Eq refl refl)
                           (iext (λ x →
                                    proof
                                      cmp3 ∙4 ((HMap L (cmp2 ∙3 (HMap J cmp1))))
                                      ≅⟨ cong (λ x₁ → cmp3 ∙4 x₁) (fcomp L) ⟩
                                      cmp3 ∙4 (HMap L cmp2 ∙4 (HMap L (HMap J cmp1)))
                                      ≅⟨ sym (Cat.ass C4) ⟩
                                      (cmp3 ∙4 HMap L cmp2) ∙4 (HMap L (HMap J cmp1)) ∎))


-- ley de intercambio
interchange : ∀{a b c d e f}{C : Cat {a} {b}}{D : Cat {c} {d}}{E : Cat {e} {f}}
               {F G H : Fun C D}{I J K : Fun D E}
              → (α : NatT F G) → (β : NatT G H)
              → (γ : NatT I J) → (δ : NatT J K)
              → compHNat (compVNat β α) (compVNat δ γ) ≅ compVNat (compHNat β δ) (compHNat α γ)
interchange {D = D}{E}{I = I}{J} (natural α _) (natural β _) (natural γ natγ) (natural δ _) =
          let open NatT
              _∙D_ = Cat._∙_ D
              open Cat E
           in
           NatTEq (iext (λ x → proof
                               (δ ∙ γ) ∙ HMap I (β ∙D α)
                               ≅⟨ cong (λ x₁ → (δ ∙ γ) ∙ x₁) (fcomp I) ⟩
                               (δ ∙ γ) ∙ (HMap I β ∙ HMap I α)
                               ≅⟨ ass ⟩
                               δ ∙ (γ ∙ (HMap I β ∙ HMap I α))
                               ≅⟨ cong (λ x₁ → δ ∙ x₁) (sym ass) ⟩
                               δ ∙ ((γ ∙ HMap I β) ∙ HMap I α)
                               ≅⟨ cong (λ x₁ → δ ∙ (x₁ ∙ HMap I α)) (sym natγ) ⟩
                               δ ∙ ((HMap J β ∙ γ) ∙ HMap I α)
                               ≅⟨ cong (λ x₁ → δ ∙ x₁) ass ⟩
                               δ ∙ (HMap J β ∙ (γ ∙ HMap I α))
                               ≅⟨ sym ass ⟩
                               (δ ∙ HMap J β) ∙ (γ ∙ HMap I α) ∎))
