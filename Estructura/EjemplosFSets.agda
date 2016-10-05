
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

module Nat where

  open Fun Nat
  open import Functors.Algebra Nat
  open F-homomorphism
  open F-algebra


  -- definir constructores
  0N : μF
  0N = {!!}

  sucN : μF → μF
  sucN x = {!!}


{- Probar que el portador de la semántica de algebra inicial
  de OnePlus es igual a ℕ
-}

   
  lemaNat : Iso Sets (fold {!!})
  lemaNat = {!!}

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

