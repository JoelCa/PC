open import Categories
open import Categories.Initial
import Functors.Algebra
open import Functors

module PropFAlgebras {a}{b}{C : Cat {a}{b}}
                           {F : Fun C C}
     where

open import Library hiding (_×_)
open import Naturals
open import Functors.Algebra F

open Cat C
open Fun F
open F-algebra
open F-homomorphism


--------------------------------------------------
-- Propiedades
--------------------------------------------------

iden-α : fold α ≅ iden {μF} 
iden-α = {!!}

-- Fusion
fusion : ∀{A B}{f : Hom (OMap A) A}{g : Hom (OMap B) B}{h : Hom A B}
      → h ∙ f ≅ g ∙ HMap h → h ∙ fold f ≅ fold g
fusion = {!!}
--
isfold : ∀{A}{f : Hom μF A}{g : Hom A μF}
      → g ∙ f ≅ iden {μF} → Σ[ h ∈ Hom (OMap A) A ] (f ≅ fold h)
isfold = {!!}
--
.roll : ∀{A B}{f : Hom B A}{g : Hom (OMap A) B}
     → fold (f ∙ g) ≅ f ∙ fold (g ∙ HMap f)
roll = {!!}

--------------------------------------------------
-- Propiedades de álgebras iniciales en categorías
-- con oroductos
--------------------------------------------------

open import Categories.Products

module ProductProperties (prod : Products C) where

--
-- Banana split
-- Nos permite transformar dos folds en uno solo
-- Ayuda : usar fusion de productos (fusionP)
 open Products prod
 open import Categories.Products.Properties prod renaming (fusion to fusionP)

 banana-split : ∀{A B}{f : Hom (OMap A) A}{g : Hom (OMap B) B}
             → ⟨ fold f , fold g ⟩ ≅ fold ⟨ f ∙ HMap π₁ , g ∙ HMap π₂ ⟩
 banana-split = {!!}
--
-- Recursion mutua
 mutua1 : ∀{A B}{f : Hom μF A}{g : Hom μF B}{h : Hom (OMap (A × B)) A}{k : Hom (OMap (A × B)) B} 
       → f ∙ α ≅ h ∙ HMap ⟨ f , g ⟩
       → g ∙ α ≅ k ∙ HMap ⟨ f , g ⟩
       → ⟨ f , g ⟩ ≅ fold ⟨ h , k ⟩
 mutua1 = {!!}

 mutua2 : ∀{A B}{f : Hom μF A}{g : Hom μF B}{h : Hom (OMap (A × B)) A}{k : Hom (OMap (A × B)) B} 
       → ⟨ f , g ⟩ ≅ fold ⟨ h , k ⟩
       → Library._×_ (f ∙ α ≅ h ∙ HMap ⟨ f , g ⟩) (g ∙ α ≅ k ∙ HMap ⟨ f , g ⟩)
 mutua2 = ?
