module Library where

open import Function using (id; _∘_; _$_) public

--open import Relation.Binary.HeterogeneousEquality public
--open ≅-Reasoning renaming (begin_ to proof_) public

open import Data.Product renaming (proj₁ to fst; proj₂ to snd) public
open import Data.Empty public using (⊥; ⊥-elim)
open import Data.Unit public using (⊤)
open import Data.Nat public using (ℕ; zero; suc; _+_; module ℕ)
open import Data.Nat.Properties.Simple public
open import Data.Fin public using (Fin; zero; suc; raise)
                            renaming (_+_ to _F+_; fromℕ to fromNat)
open import Level public renaming (suc to lsuc; zero to lzero) hiding (lift)

--------------------------------------------------
-- Heterogeneous equality

module HeterogeneousEquality where
 open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
 open import Relation.Binary

 infix 4 _≅_

 data _≅_ {ℓ} {A : Set ℓ} (x : A) : {B : Set ℓ} → B → Set where
   refl : x ≅ x

 -- Conversion
 ≅-to-≡ : ∀ {a} {A : Set a} {x y : A} → x ≅ y → x ≡ y
 ≅-to-≡ refl = refl

 reflexive : ∀ {a} {A : Set a} → _⇒_ {A = A} _≡_ (λ x y → x ≅ y)
 reflexive refl = refl

 sym : ∀ {ℓ} {A B : Set ℓ} {x : A} {y : B} → x ≅ y → y ≅ x
 sym refl = refl

 trans : ∀ {ℓ} {A B C : Set ℓ} {x : A} {y : B} {z : C} →
        x ≅ y → y ≅ z → x ≅ z
 trans refl eq = eq

 subst : ∀ {a} {A : Set a} {p} → Substitutive {A = A} (λ x y → x ≅ y) p
 subst P refl p = p

 subst₂ : ∀ {a b p} {A : Set a} {B : Set b} (P : A → B → Set p) →
         ∀ {x₁ x₂ y₁ y₂} → x₁ ≅ x₂ → y₁ ≅ y₂ → P x₁ y₁ → P x₂ y₂
 subst₂ P refl refl p = p

 subst-removable : ∀ {a p} {A : Set a}
                  (P : A → Set p) {x y} (eq : x ≅ y) z →
                  subst P eq z ≅ z
 subst-removable P refl z = refl

 ≡-subst-removable : ∀ {a p} {A : Set a}
                    (P : A → Set p) {x y} (eq : x ≡ y) z →
                    P.subst P eq z ≅ z
 ≡-subst-removable P refl z = refl

 cong : ∀ {a b} {A : Set a} {B : A → Set b} {x y}
       (f : (x : A) → B x) → x ≅ y → f x ≅ f y
 cong f refl = refl

 cong-app : ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
           f ≅ g → (x : A) → f x ≅ g x
 cong-app refl x = refl

 cong₂ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c}
          {x y u v}
        (f : (x : A) (y : B x) → C x y) → x ≅ y → u ≅ v → f x u ≅ f y v
 cong₂ f refl refl = refl

--------------------------------------------------

 module ≅-Reasoning where

  -- The code in Relation.Binary.EqReasoning cannot handle
  -- heterogeneous equalities, hence the code duplication here.

  infix  4 _IsRelatedTo_
  infix  3 _∎
  infixr 2 _≅⟨_⟩_ _≡⟨_⟩_ _≡⟨⟩_
  infix  1 proof_

  data _IsRelatedTo_ {ℓ} {A : Set ℓ} (x : A) {B : Set ℓ} (y : B) :
                     Set ℓ where
    relTo : (x≅y : x ≅ y) → x IsRelatedTo y

  proof_ : ∀ {ℓ} {A : Set ℓ} {x : A} {B} {y : B} →
           x IsRelatedTo y → x ≅ y
  proof relTo x≅y = x≅y

  _≅⟨_⟩_ : ∀ {ℓ} {A : Set ℓ} (x : A) {B} {y : B} {C} {z : C} →
           x ≅ y → y IsRelatedTo z → x IsRelatedTo z
  _ ≅⟨ x≅y ⟩ relTo y≅z = relTo (trans x≅y y≅z)

  _≡⟨_⟩_ : ∀ {ℓ} {A : Set ℓ} (x : A) {y C} {z : C} →
           x ≡ y → y IsRelatedTo z → x IsRelatedTo z
  _ ≡⟨ x≡y ⟩ relTo y≅z = relTo (trans (reflexive x≡y) y≅z)

  _≡⟨⟩_ : ∀ {ℓ} {A : Set ℓ} (x : A) {B} {y : B} →
          x IsRelatedTo y → x IsRelatedTo y
  _ ≡⟨⟩ x≅y = x≅y

  _∎ : ∀ {a} {A : Set a} (x : A) → x IsRelatedTo x
  _∎ _ = relTo refl

open HeterogeneousEquality public
open ≅-Reasoning public 

--------------------------------------------------
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
 

