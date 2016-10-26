
module EjemplosFSets where

open import Categories.Iso
open import Categories.Sets
open import Categories.Products
open import Categories.Coproducts
open import Categories.Terminal
open import Categories.Initial
open import Functors
open import Functors.Constant
open import Library hiding (_×_ ; _+_)

open Products (SetsHasProducts {lzero})
open Coproducts (SetsHasCoproducts {lzero}) 
open Terminal OneSet
open Initial ZeroSet

open import Functors.Product (SetsHasProducts {lzero})
open import Functors.Coproduct (SetsHasCoproducts {lzero})


--------------------------------------------------
{- Definir el siguiente funtor sobre Sets
 *usando suma y producto de functores*
 La idea es reusarlo que ya está definido.
 *No* definir functores usando el constructor de funtores.
  -}

-- Nat X = 1 + X
Nat : Fun Sets Sets
Nat = (K ⊤) +F IdF

open import Categories

equalPair : ∀{A B C}{f h : Cat.Hom Sets A B}{g i : Cat.Hom Sets C B}
          → [ f , g ] ≅ [ h , i ] → (f ≅ h) × (g ≅ i)
equalPair {f = f} {h} {g} {i} x =
    (proof
      f
      ≅⟨ sym (Coproducts.law1 SetsHasCoproducts {f = f} {g}) ⟩ 
      [ f , g ] ∘ inl
      ≅⟨ cong (λ x₁ → x₁ ∘ inl) x ⟩
      [ h , i ] ∘ inl
      ≅⟨ sym (Coproducts.law1 SetsHasCoproducts {f = h} {i}) ⟩
      h ∎) ,
    (proof
      g
      ≅⟨ sym (Coproducts.law2 SetsHasCoproducts {f = f} {g}) ⟩ 
      [ f , g ] ∘ inr
      ≅⟨ cong (λ x₁ → x₁ ∘ inr) x ⟩
      [ h , i ] ∘ inr
      ≅⟨ sym (Coproducts.law2 SetsHasCoproducts {f = h} {i}) ⟩
      i ∎)
    

module Fold where

  FunF = (K ⊤) +F IdF
  
  open Fun FunF
  open import Functors.Algebra FunF
  open F-homomorphism
  open F-algebra
  open import Categories.Coproducts.Properties (SetsHasCoproducts {lzero})

              
  foldProp : {A : Set}  {h : Cat.Hom Sets (OMap A) A}
            → [ (fold h) ∘ (α ∘ inl) , (fold h) ∘ (α ∘ inr) ] ≅
              [ h ∘ inl , (h ∘ inr) ∘ (fold h)]
  foldProp {h = h} = proof
                     [ (fold h) ∘ (α ∘ inl) , (fold h) ∘ (α ∘ inr) ]
                     ≅⟨ sym (dist-izq {h = fold h}) ⟩
                     (fold h) ∘ [ α ∘ inl , α ∘ inr ]
                     ≅⟨ cong (λ x → (fold h) ∘ x)
                             (sym (Coproducts.law3 SetsHasCoproducts refl refl)) ⟩
                     (fold h) ∘ α
                     ≅⟨ homo-prop init-homo ⟩
                     h ∘ HMap (fold h)
                     ≅⟨ cong (λ x → x ∘ HMap (fold h))
                             (Coproducts.law3 SetsHasCoproducts
                               {f = h ∘ inl} {g = h ∘ inr} {h = h} refl refl) ⟩
                     [ h ∘ inl , h ∘ inr ] ∘ HMap (fold h)
                     ≅⟨ fusion-cop ⟩
                     [(h ∘ inl) ∘ id , (h ∘ inr) ∘ (fold h) ]
                     ≅⟨ refl ⟩
                     [ h ∘ inl , (h ∘ inr) ∘ (fold h) ] ∎


  foldProp₀ : {A : Set}  {h : Cat.Hom Sets (OMap A) A}
            → (fold h) ∘ (α ∘ inl) ≅ h ∘ inl
  foldProp₀ = fst (equalPair foldProp)

  foldProp₁ : {A : Set}  {h : Cat.Hom Sets (OMap A) A}
            → (fold h) ∘ (α ∘ inr) ≅ (h ∘ inr) ∘ (fold h)
  foldProp₁ = snd (equalPair foldProp)


module Nat where

  open Fun Nat
  open import Functors.Algebra Nat
  open F-homomorphism
  open F-algebra


  -- definir constructores
  0N : μF
  0N = (α ∘ inl) _

  sucN : μF → μF
  sucN = α ∘ inr


{- Probar que el portador de la semántica de algebra inicial
  de OnePlus es igual a ℕ
-}

  NatμF : ℕ → μF
  NatμF zero = 0N
  NatμF (suc x) = sucN (NatμF x)

  foldNat = fold {ℕ} ([ (λ x → 0) , suc ])

  open Fold

  lemaNatId₀ : {n : ℕ} → (foldNat ∘ NatμF) n ≅ n
  lemaNatId₀ {zero} = proof
                      foldNat 0N
                      ≅⟨ cong-app foldProp₀ _ ⟩
                      0 ∎
  lemaNatId₀ {suc n} = proof 
                       foldNat (sucN (NatμF n)) 
                       ≅⟨ cong-app foldProp₁ (NatμF n) ⟩ 
                       suc (foldNat (NatμF n))
                       ≅⟨ cong (λ x → suc x) (lemaNatId₀ {n}) ⟩
                       suc n ∎

  
  natAlgebra = falgebra ℕ [ (λ x → 0) , suc ]
  
  Nat→μFHomo : F-homomorphism natAlgebra inF
  Nat→μFHomo = homo NatμF (ext (λ { (Inl x) → refl ; (Inr x) → refl }))

  
  lemaNatId₁ : (NatμF ∘ foldNat) ≅ id
  lemaNatId₁ = homomorphismEqApp (iden-homo-inF-inF (comp-homo Nat→μFHomo init-homo))

  lemaNat : Iso Sets (fold {ℕ} ([ (λ x → 0) , suc ]))
  lemaNat = iso NatμF
                (ext (λ n → lemaNatId₀))
                lemaNatId₁

--------------------------------------------------
{- Definir un functor cuya algebra inicial sea las listas.
-}

L : (A : Set) → Fun Sets Sets
L A = (K ⊤) +F ((K A) ×F IdF)

module Listas (A : Set) where

  open Fun (L A)
  open import Functors.Algebra (L A)
  open F-homomorphism
  open F-algebra
  open import Categories
  open import Categories.Coproducts.Properties (SetsHasCoproducts {lzero})

{-
   Definir constructores, y probar que
   efectivamente son listas (como hicimos con los naturales)
-}

  foldPropL : {A : Set}  {h : Cat.Hom Sets (OMap A) A}
            → [ (fold h) ∘ (α ∘ inl) , (fold h) ∘ (α ∘ inr) ] ≅
              [ h ∘ inl , (h ∘ inr) ∘ pair id (fold h)]
  foldPropL {h = h} = proof
                     [ (fold h) ∘ (α ∘ inl) , (fold h) ∘ (α ∘ inr) ]
                     ≅⟨ sym (dist-izq {h = fold h}) ⟩
                     (fold h) ∘ [ α ∘ inl , α ∘ inr ]
                     ≅⟨ cong (λ x → (fold h) ∘ x)
                             (sym (Coproducts.law3 SetsHasCoproducts refl refl)) ⟩
                     (fold h) ∘ α
                     ≅⟨ homo-prop init-homo ⟩
                     h ∘ HMap (fold h)
                     ≅⟨ cong (λ x → x ∘ HMap (fold h))
                             (Coproducts.law3 SetsHasCoproducts
                               {f = h ∘ inl} {g = h ∘ inr} {h = h} refl refl) ⟩
                     [ h ∘ inl , h ∘ inr ] ∘ HMap (fold h)
                     ≅⟨ fusion-cop ⟩
                     [(h ∘ inl) ∘ id , (h ∘ inr) ∘ pair id (fold h) ]
                     ≅⟨ refl ⟩
                     [ h ∘ inl , (h ∘ inr) ∘ pair id (fold h) ] ∎

  foldPropL₀ : {A : Set}  {h : Cat.Hom Sets (OMap A) A}
            → (fold h) ∘ (α ∘ inl) ≅ h ∘ inl
  foldPropL₀ = fst (equalPair foldPropL)

  foldPropL₁ : {A : Set}  {h : Cat.Hom Sets (OMap A) A}
             → (fold h) ∘ (α ∘ inr) ≅ (h ∘ inr) ∘ pair id (fold h)
  foldPropL₁ = snd (equalPair foldPropL)

  nilL : μF
  nilL = (α ∘ inl) _

  consL : A × μF → μF
  consL = α ∘ inr
  

  open import Data.List hiding (length) public 
  
  ListμF : List A → μF
  ListμF [] = nilL
  ListμF (x ∷ xs) = consL (x , ListμF xs)


  foldList = fold {List A} ([_,_] (λ x → []) (λ { (c , xs) → c ∷ xs }))

  lemaListId₀ : {xs : List A} → (foldList ∘ ListμF) xs ≅ xs
  lemaListId₀ {[]} = cong-app foldPropL₀ _
  lemaListId₀ {x ∷ xs} = proof
                         foldList (consL (x , ListμF xs) )
                         ≅⟨ cong-app foldPropL₁ (x , ListμF xs) ⟩
                         ((λ { (c , xs) → c ∷ xs }) ∘ pair id foldList) (x , ListμF xs)
                         ≅⟨ refl ⟩
                         ((λ { (c , xs) → c ∷ xs }) ∘ (λ { (a , b) → id a , foldList b }))
                           ( x , ListμF xs)
                         ≅⟨ refl ⟩
                         x ∷  foldList (ListμF xs)
                         ≅⟨ cong (λ y → x ∷ y) (lemaListId₀ {xs}) ⟩
                         x ∷ xs ∎


  listAlgebra = falgebra (List A) ([_,_] (λ x → []) (λ { (c , xs) → c ∷ xs }))

  List→μFHomo : F-homomorphism listAlgebra inF
  List→μFHomo = homo ListμF (ext (λ { (Inl x) → refl ; (Inr x) → refl }))

  lemaListId₁ : (ListμF ∘ foldList) ≅ id
  lemaListId₁ = homomorphismEqApp (iden-homo-inF-inF (comp-homo List→μFHomo init-homo))

  lemaList : Iso Sets (fold {List A} ([_,_] (λ x → []) (λ { (c , xs) → c ∷ xs })))
  lemaList = iso ListμF
                 (ext (λ _ → lemaListId₀))
                 lemaListId₁

{-
  Definir la función length para listas
-}

  lengthList : List A → ℕ
  lengthList [] = 0
  lengthList (x ∷ xs) = suc (lengthList xs)

  length : μF → ℕ
  length = lengthList ∘ (fold {List A} ([_,_] (λ x → []) (λ { (c , xs) → c ∷ xs })))

