
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

--Esto está bien?
-- Nat X = 1 + X
Nat : Fun Sets Sets
Nat = (K ⊤) +F IdF

module Nat where

  open Fun Nat
  open import Functors.Algebra Nat
  open F-homomorphism
  open F-algebra


  --están bien?
  
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

  h = fold {ℕ} ([ (λ x → 0) , suc ])

  open import Categories.Coproducts.Properties (SetsHasCoproducts {lzero})

  lemazo : [ h ∘ (α ∘ inl) , h ∘ sucN ] ≅ [ (λ x → 0) , suc ∘ h ]
  lemazo = proof
           [ h ∘ (α ∘ inl) , h ∘ sucN ]
           ≅⟨ sym (lema-cop {h = h}) ⟩
           h ∘ [ α ∘ inl , sucN ]
           ≅⟨ cong (λ x → h ∘ x)
                   (sym (Coproducts.law3 SetsHasCoproducts refl refl)) ⟩
           h ∘ α
           ≅⟨ homo-prop init-homo ⟩
           [ (λ x → 0) , suc ] ∘ HMap h
           ≅⟨ fusion-cop ⟩
           [(λ x → 0) ∘ id , suc ∘ h ]
           ≅⟨ refl ⟩
           [ (λ x → 0) , suc ∘ h ] ∎

  
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


  lemaNatId₀ : {n : ℕ} → (h ∘ NatμF) n ≅ n
  lemaNatId₀ {zero} = proof
                      h 0N
                      ≅⟨ cong-app (fst (equalPair lemazo)) _ ⟩
                      0 ∎
  lemaNatId₀ {suc n} = proof 
                       h (sucN (NatμF n)) 
                       ≅⟨ cong-app (snd (equalPair lemazo)) (NatμF n) ⟩ 
                       suc (h (NatμF n))
                       ≅⟨ cong (λ x → suc x) (lemaNatId₀ {n}) ⟩
                       suc n ∎

  
  natAlgebra = falgebra ℕ [ (λ x → 0) , suc ]
  
  NatμFIsHomo : F-homomorphism natAlgebra inF
  NatμFIsHomo = homo NatμF (ext (λ { (Inl x) → refl ; (Inr x) → refl }))
  

  lemaNatId₁ : { u : μF} → (NatμF ∘ h) u ≅ u
  lemaNatId₁ {u} = {!!}

  lemaNat : Iso Sets (fold {ℕ} ([ (λ x → 0) , suc ]))
  lemaNat = iso NatμF
                (ext (λ n → lemaNatId₀))
                {!!}

--------------------------------------------------
{- Definir un functor cuya algebra inicial sea las listas.
-}

L : (A : Set) → Fun Sets Sets
L A = {!!}

module Listas (A : Set) where

  open Fun (L A)
  open import Functors.Algebra (L A)
  open F-homomorphism
  open F-algebra

{-
   Definir constructores, y probar que
   efectivamente son listas (como hicimos con los naturales)
-}


  


{-
  Definir la función length para listas
-}

  length : μF → ℕ
  length = {!!}

