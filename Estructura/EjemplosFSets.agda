
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

  lemaNat₀ : ℕ → μF
  lemaNat₀ zero = 0N
  lemaNat₀ (suc x) = sucN (lemaNat₀ x)

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

  -- lemaNatId₀ : {n : ℕ} → (fold [ (λ x → 0) , suc ] ∘ lemaNat₀) n ≅ id n
  -- lemaNatId₀ {zero} = proof
  --                     fold [ (λ x → 0) , suc ] 0N
  --                     ≅⟨ {!!} ⟩
  --                     {!!} ≅⟨ {!!} ⟩ {!!} ≅⟨ {!!} ⟩ {!!} ∎
  -- lemaNatId₀ {suc n} = {!!}
  

  lemaNat : Iso Sets (fold {ℕ} ([ (λ x → 0) , suc ]))
  lemaNat = iso lemaNat₀
                (ext (λ n → {!!}))
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

