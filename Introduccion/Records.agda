
module Records where

open import Relation.Binary.HeterogeneousEquality

postulate ext : ∀{a b}{A : Set a}{B B' : A → Set b}
                {f : ∀ a → B a}{g : ∀ a → B' a} → 
                (∀ a → f a ≅ g a) → f ≅ g


{- Veremos, el uso de records para definir estructuras algebraicas -}

{- Notar el uso de de Set₁ en lugar de Set ya que tenemos que
 situarnos en el nivel siguiente a Set₀ = Set, para hablar de cosas en
 Set (como carrier).

Los subindices son ₀ = \_0 y ₁ = \_1

 -}


record Monoid : Set₁  where
  infixr 7 _∙_
  field  Carrier : Set
         _∙_     : Carrier → Carrier → Carrier  {- ∙ = \. -}
         ε       : Carrier
         lid     : {x : Carrier} → ε ∙ x ≅ x
         rid     : {x : Carrier} → x ∙ ε ≅ x
         assoc   : {x y z : Carrier} → (x ∙ y) ∙ z ≅ x ∙ (y ∙ z) 

{- ¿Qué sucede si queremos usar un Carrier en Set₁? ¿o en Set₂? -}


open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties.Simple
{- propiedades simples de la suma, como por ejemplo
 +-right-identity, y +-assoc
-}

-- Monoide de Naturales y suma

module NatMonoid where

  NatMonoid : Monoid
  NatMonoid = record
                { Carrier = ℕ
                ; _∙_ = _+_
                ; ε = 0
                ; lid = refl
                ; rid = λ{x} → ≡-to-≅ (+-right-identity x)
                ; assoc = λ {x} {y} {z} → ≡-to-≅ (+-assoc x y z) }

{- ≡-to-≅ convierte igualdad proposicional en heterogénea -}

open NatMonoid

--------------------------------------------------
{- Ejercicio: Probar que las listas son un monoide -}

open ≅-Reasoning renaming (begin_ to proof_)

data List (A : Set) : Set where
   [] : List A
   _∷_ : (x : A) → (xs : List A) → List A

infixl 5 _∷_

-- NO se puede
-- open import Intro
_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

++[] : {A : Set} (x : List A) → x ++ [] ≅ x
++[] [] = refl
++[] (x ∷ xs) = proof
                 x ∷ (xs ++ [])
                 ≅⟨ cong (λ ys -> x ∷ ys) (++[] xs) ⟩
                 x ∷ xs
                 ∎

++assoc : {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≅ xs ++ (ys ++ zs)
++assoc [] ys zs = refl
++assoc (x ∷ xs) ys zs = proof
                         x ∷ ((xs ++ ys) ++ zs)
                         ≅⟨ cong (λ ws -> x ∷ ws) (++assoc xs ys zs) ⟩
                         x ∷ (xs ++ (ys ++ zs))
                         ∎

ListMonoid : Set -> Monoid
ListMonoid X = record
                { Carrier = List X
                ; _∙_ = _++_
                ; ε = []
                ; lid = refl
                ; rid = λ {x} → ++[] x
                ; assoc = λ {x} {y} {z} → ++assoc x y z }

--------------------------------------------------

{- Ejercicio: Probar que para todo monoide M, N, el producto
   cartesiano de los respectivos soportes (Carrier M × Carrier N)
   es  el soporte de un monoide

 Ayuda : puede ser útil cong₂
-}

open import Data.Product

ProdMonoid : Monoid → Monoid -> Monoid
ProdMonoid X Y = record
                   { Carrier = Carrier₁ × Carrier₂
                   ; _∙_ = λ x y → _∙₁_ (proj₁ x) (proj₁ y) , _∙₂_ (proj₂ x) (proj₂ y)
                   ; ε = ε₁ , ε₂
                   ; lid = cong₂ (λ x y → x , y) (Monoid.lid X) (Monoid.lid Y)
                   ; rid = cong₂ (λ x y → x , y) (Monoid.rid X) (Monoid.rid Y)
                   ; assoc = cong₂ (λ x y → x , y) (Monoid.assoc X) (Monoid.assoc Y) }
                 where
                   open Monoid X renaming (Carrier to Carrier₁; ε to ε₁ ;  _∙_ to _∙₁_)
                   open Monoid Y renaming (Carrier to Carrier₂; ε to ε₂ ;  _∙_ to _∙₂_)
   
--------------------------------------------------
open import Function

-- Monoide de endofunciones
EndoMonoid : Set → Monoid
EndoMonoid X = record
                 { Carrier = X → X
                 ; _∙_ = _∘′_
                 ; ε = id
                 ; lid = refl
                 ; rid = refl
                 ; assoc = refl }


module Cayley where

  open Monoid using (Carrier)

  Cayley : Monoid → Monoid
  Cayley M = EndoMonoid (Carrier M) 

  rep : (M : Monoid) → Carrier M → Carrier (Cayley M)
  rep M x = λ y → x ∙ y
           where open Monoid M

  abs : (M : Monoid) → Carrier (Cayley M) → Carrier M
  abs M f = f ε
           where open Monoid M

  lemma : (M : Monoid) → {x : Carrier M} →
          abs M (rep M x) ≅ x
  lemma M = rid
           where open Monoid M

module Monoid-Homomorphism where
 open Monoid

-- Homomorfismos de monoides
 record Is-Monoid-Homo {M N : Monoid}(morph : Carrier M → Carrier N) : Set where
   constructor _,_
   open Monoid M renaming (ε to ε₁ ;  _∙_ to _∙₁_)
   open Monoid N renaming (ε to ε₂ ;  _∙_ to _∙₂_)
   --constructor _,_
   field
    preserves-unit : morph ε₁ ≅ ε₂
    preserves-mult : ∀{x y} → morph (x ∙₁ y) ≅ morph x ∙₂ morph y 

open Monoid-Homomorphism
open Cayley

rep-is-monoid-homo : {M : Monoid} → Is-Monoid-Homo {M} {Cayley M} (rep M)
rep-is-monoid-homo {M} = record {
                         preserves-unit = ext (λ y → lid)
                         ; preserves-mult = ext (λ a → assoc) }
                         where open Monoid M

--------------------------------------------------
{- Ejercicio: Probar que length es un homorfismo de monoides -}

length : {A : Set} → List A → ℕ
length [] = 0
length (x ∷ xs) = 1 + length xs

lema-length : {A : Set} -> (xs ys : List A) -> length (xs ++ ys) ≅ length xs + length ys
lema-length [] ys = refl
lema-length (x ∷ xs) ys = cong suc (lema-length xs ys)


length-is-monoid-homo : {A : Set} → Is-Monoid-Homo {ListMonoid (List A)} {NatMonoid} (length)
length-is-monoid-homo = record {
                               preserves-unit = refl
                               ; preserves-mult = λ {x y} → lema-length x y }
              
--------------------------------------------------
module Foldr (M : Monoid) where

 open Monoid M

 {- Ejercicio : Definir foldr y probar que (foldr _∙_ ε) es un homorfismo de monoides -}

 foldr : {A B : Set} → (A → B → B) → B → List A → B
 foldr _⊗_ e [] = e
 foldr _⊗_ e (x ∷ xs) = x ⊗ (foldr _⊗_ e xs)

 lema-foldr : {M : Monoid} {xs ys : List Carrier} → 
   foldr (_∙_) ε (xs ++ ys) ≅ (foldr (_∙_) ε xs) ∙  (foldr (_∙_) ε ys)
 lema-foldr {xs = []} = sym lid
 lema-foldr {xs = x ∷ xs} {ys} = proof
                                 x ∙ foldr _∙_ ε (xs ++ ys)
                                 ≅⟨ cong (λ x₁ → _∙_ x x₁) (lema-foldr {M} {xs = xs} {ys}) ⟩
                                 x ∙ foldr _∙_ ε xs ∙ foldr _∙_ ε ys
                                 ≅⟨ sym assoc ⟩
                                 (x ∙ foldr _∙_ ε xs) ∙ foldr _∙_ ε ys
                                 ∎


 foldr-is-monoid-homo : Is-Monoid-Homo {ListMonoid Carrier} {M} (foldr (_∙_) (ε))
 foldr-is-monoid-homo = record {
                               preserves-unit = refl
                               ; preserves-mult = λ {xs} {ys} → lema-foldr {M} {xs} {ys}  }


--------------------------------------------------

{- Isomorfismos entre conjuntos -}

record Iso (A : Set)(B : Set) : Set where
  field fun : A → B
        inv : B → A
        law1 : ∀ b → fun (inv b) ≅ b
        law2 : ∀ a → inv (fun a) ≅ a

open Iso

-----------------------------

{- Ejercicio : introducir un tipo de datos ⊤ con un único habitante y
probar que  ℕ es isomorfo a List ⊤ -}

record ⊤ : Set where
  constructor tt


isoNatUnit-inv : ℕ → List ⊤
isoNatUnit-inv zero = []
isoNatUnit-inv (suc n) = tt ∷ isoNatUnit-inv n


lema1IsoNatUnit : {n : ℕ} → length (isoNatUnit-inv n) ≅ n
lema1IsoNatUnit {zero} = refl
lema1IsoNatUnit {suc n} = cong suc (lema1IsoNatUnit {n})

lema2IsoNatUnit : {xs : List ⊤} → isoNatUnit-inv (length xs) ≅ xs
lema2IsoNatUnit {[]} = refl
lema2IsoNatUnit {x ∷ xs} = cong (λ x₁ → x ∷ x₁) (lema2IsoNatUnit {xs})

IsoNat-ListUnit : Iso (List ⊤) ℕ
IsoNat-ListUnit = record
                  { fun = length
                    ; inv = isoNatUnit-inv
                    ; law1 = λ b → lema1IsoNatUnit {b} 
                    ; law2 = λ a → lema2IsoNatUnit {a} }


{- Ejercicio: introducir un constructor de tipos Maybe y probar que
Maybe ℕ es isomorfo a ℕ -}

-- record Maybe (A : Set) : Set where
--   constructor _,_
--   field
--     just : A
--     nothing : Maybe A

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just  : A → Maybe A

funNatIsoNat : Maybe ℕ → ℕ
funNatIsoNat nothing = 0
funNatIsoNat (just x) = suc x

invNatIsoNat : ℕ → Maybe ℕ
invNatIsoNat zero = nothing
invNatIsoNat (suc n) = just n

lema1NatIsoNat : (n : ℕ) → funNatIsoNat (invNatIsoNat n) ≅ n
lema1NatIsoNat zero = refl
lema1NatIsoNat (suc n) = refl

lema2NatIsoNat : (m : Maybe ℕ) → invNatIsoNat (funNatIsoNat m) ≅ m
lema2NatIsoNat nothing = refl
lema2NatIsoNat (just x) = refl


maybeNatIsoNat  : Iso (Maybe ℕ) ℕ
maybeNatIsoNat = record
                 { fun = funNatIsoNat
                   ; inv = invNatIsoNat
                   ; law1 = lema1NatIsoNat
                   ; law2 = lema2NatIsoNat }


{- Ejercicio: introducir un constructor de tipos _×_ para productos
cartesianos (o usar el de Data.Product) y probar que (A → B × C) es
isomorfo a (A → B) × (A → C) para todos A, B, y C, habitantes de Set -}

open import Data.Product
open import Function using (_∘′_)

prodIso : {A B C : Set} → Iso (A → B × C) ((A → B) × (A → C))
prodIso {a} {b} {c} = record
                      { fun = λ x → (proj₁ ∘ x) , (proj₂ ∘ x)
                        ; inv = λ x y → (proj₁ x y) , (proj₂ x y)
                        ; law1 = λ x → refl
                        ; law2 = λ x → refl }


-- Ejercicio: construir isomorfismos entre Vec A n × Vec B n y
-- Vec (A × B) n para todos A, B habitantes de Set y n natural

open import Data.Vec hiding (zip; unzip)

unzip : ∀ {a b n} {A : Set a} {B : Set b} →
        Vec (A × B) n → Vec A n × Vec B n
unzip []              = [] , []
unzip ((x , y) ∷ xys) with unzip xys
unzip ((x , y) ∷ xys) | (a , b) = (x ∷ a) , (y ∷ b)

zipVec : ∀ {a b n} {A : Set a} {B : Set b} →
        (Vec A n × Vec B n) → Vec (A × B) n
zipVec ([] , []) = []
zipVec ((x ∷ xs) , (y ∷ ys)) = (x , y) ∷ (zipVec (xs , ys)) 


lema1prodVecIso : {A B : Set} {n : ℕ} {v : Vec (A × B) n} → zipVec (unzip v) ≅ v
lema1prodVecIso {v = []} = refl
lema1prodVecIso {v = x ∷ v} = cong (λ x₁ → x ∷ x₁) (lema1prodVecIso {v = v})

lema2prodVecIso : {A B : Set} {n : ℕ} {x : Vec A n × Vec B n} → unzip (zipVec x) ≅ x
lema2prodVecIso {x = [] , []} = refl
lema2prodVecIso {x = (x ∷ xs) , (y ∷ ys)} = let p = lema2prodVecIso {x = xs , ys}
                                            in cong₂ Σ._,_
                                               (cong (λ z → x ∷ proj₁ z) p)
                                               (cong (λ z → y ∷ proj₂ z) p)


prodVecIso : {A B : Set} {n : ℕ} → Iso (Vec A n × Vec B n) (Vec (A × B) n)
prodVecIso = record
             { fun = zipVec
               ; inv = unzip
               ; law1 = λ x → lema1prodVecIso {v = x}
               ; law2 = λ x → lema2prodVecIso {x = x} }
