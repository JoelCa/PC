module Library where

open import Function using (id; _∘_; _$_) public
open import Relation.Binary.HeterogeneousEquality public
open ≅-Reasoning renaming (begin_ to proof_) public
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) public
open import Data.Empty public using (⊥; ⊥-elim)
open import Data.Unit public using (⊤)
open import Data.Nat public using (ℕ; zero; suc; _+_; module ℕ)
open import Data.Nat.Properties.Simple public
open import Data.Fin public using (Fin; zero; suc; raise)
                            renaming (_+_ to _F+_; fromℕ to fromNat)
open import Level public renaming (suc to lsuc; zero to lzero; lift to llift)


dcong : ∀{a b}{A A' : Set a}{B : A → Set b}{B' : A' → Set b}
        {f : (a : A) → B a}{f' : (a : A') → B' a}{a : A}{a' : A'} → 
        a ≅ a' → B ≅ B' → f ≅ f' → f a ≅ f' a'
dcong refl refl refl = refl

dicong : ∀{a b}{A A' : Set a}{B : A → Set b}{B' : A' → Set b}
         {f : ∀ {a} → B a}{f' : ∀ {a} → B' a} → {a : A}{a' : A'} → 
         a ≅ a' →  B ≅ B' → 
         (λ {a} → f {a}) ≅ (λ {a} → f' {a}) → 
         f {a} ≅ f' {a'}
dicong refl refl refl = refl

ifcong : ∀{a b}{A : Set a}{B : A → Set b}{f f' : {x : A} → B x}(a : A) → 
         _≅_ {_}{ {x : A} → B x} f { {x : A} → B x} f' → f {a} ≅ f' {a}
ifcong a refl = refl

cong₃ : ∀{a b c d}{A : Set a}{B : A → Set b}
        {C : ∀ x → B x → Set c }{D : ∀ x y → C x y → Set d}
        (f : ∀ x y z → D x y z)
        {a a' : A} → a ≅ a' → 
        {b : B a}{b' : B a'} → b ≅ b' → 
        {c : C a b}{c' : C a' b'} → c ≅ c' → 
        f a b c ≅ f a' b' c'
cong₃ f refl refl refl = refl

ir : ∀ {ℓ} {A B : Set ℓ} {x : A} {y : B}
                    (p q : x ≅ y) → p ≅ q
ir refl refl = refl


{- extensionalidad -}
postulate ext : ∀{a b}{A : Set a}{B B' : A → Set b}
                {f : ∀ a → B a}{g : ∀ a → B' a} → 
                (∀ a → f a ≅ g a) → f ≅ g


{- extensionalidad para funciones con argumento implícito -}
postulate iext : ∀{a b}{A : Set a}{B B' : A → Set b}
             {f : ∀ {a} → B a}{g : ∀{a} → B' a} → 
             (∀ a → f {a} ≅ g {a}) → 
             _≅_ {_}{ {a : A} → B a} f { {a : A} → B' a} g

iir : ∀ {a b} {I : Set a}{A B : I → Set b}{x : {i : I} → A i} {y : {i : I} → B i}
                    (p q : ∀{i} → x {i} ≅ y {i}) →
                    _≅_ {_} { {i : I} → _} p { {i : I} → _} q
iir p q = iext (λ i → ir (p {i}) (q {i}))

i2ir : ∀ {a b} {I J : Set a}{A B : I → J → Set b}
       {x : {i : I} → {j : J}→ A i j}
       {y : {i : I} → {j : J} → B i j}
                    (p q : ∀{i j} → x {i} {j} ≅ y {i} {j}) →
                    _≅_ {_} { {i : I} → {j : J} → _} p { {i : I} → {j : J} → _} q
i2ir p q = iext (λ i → iext ( λ j →  ir ( (p {i} {j}) ) ( (q {i} {j}) )  ))
 

