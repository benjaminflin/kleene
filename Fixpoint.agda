open import Level renaming (suc to ℓsuc ; zero to ℓ₀)  
open import Relation.Binary.Core

module Fixpoint where

open import Data.Nat renaming (_⊔_ to max)
open import Relation.Binary.Structures 

record IsIncreasing {a ℓ} {A : Set a} (f : ℕ → A) (_≲_ : Rel A ℓ) : Set (a ⊔ ℓ) where
    field 
        increases : ∀ {m n} → m ≤ n → f m ≲ f n

record Increasing {a ℓ} {A : Set a} (_≲_ : Rel A ℓ) : Set (a ⊔ ℓ) where
    field
        sequence : ℕ → A 
        isIncreasing : IsIncreasing sequence _≲_
    
    open IsIncreasing isIncreasing public 

open Increasing

record IsDirected {a ℓ ℓ₂} {A : Set a} (_≈_ : Rel A ℓ) (_≲_ : Rel A ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂) where  
    field
        isPartialOrder : IsPartialOrder _≈_ _≲_
        sup : Increasing _≲_ → A 
        supIsUpperBound : ∀ s n → (sequence s) n ≲ sup s   
        supIsLeastUpperBound : ∀ {k} s → (∀ n → (sequence s) n ≲ k) → sup s ≲ k
        ⊥ : A  
        ⊥isLeast : ∀ x → ⊥ ≲ x

    open IsPartialOrder isPartialOrder public

record Directed a ℓ ℓ₂ : Set (ℓsuc (a ⊔ ℓ ⊔ ℓ₂)) where
    field
        Carrier : Set a 
        _≈_ : Rel Carrier ℓ
        _≲_ : Rel Carrier ℓ₂
        isDirected : IsDirected _≈_ _≲_   
    
    open IsDirected isDirected public 

module _ {a ℓ ℓ₂} (dir : Directed a ℓ ℓ₂) where

    open Directed dir renaming (Carrier to A; refl to ≲refl; trans to ≲trans)

    record IsMonotone (f : A → A) : Set (a ⊔ ℓ ⊔ ℓ₂) where
        field
            monotonicity : ∀ {x y} → x ≲ y → f x ≲ f y

    record Monotone : Set (a ⊔ ℓ ⊔ ℓ₂) where
        field
            function : A → A
            isMonotone : IsMonotone function 

        open IsMonotone isMonotone public

    open import Function.Base 



    _⊚_ : Monotone → Increasing _≲_ → Increasing _≲_
    f ⊚ g = record 
        { sequence = function ∘ sequence g 
        ; isIncreasing = record { increases = monotonicity ∘ increases g } }
        where open Monotone f
    
    record IsScottContinuous (f : A → A) : Set (a ⊔ ℓ ⊔ ℓ₂) where
        field 
            isMonotone : IsMonotone f 
        
        monotone : Monotone
        monotone = record { isMonotone = isMonotone }

        field
            continuity : ∀ s → f (sup s) ≈ sup (monotone ⊚ s)
        
        open IsMonotone isMonotone public
    
    record ScottContinuous : Set (a ⊔ ℓ ⊔ ℓ₂) where 
        field
            function : A → A 
            isScottContinuous : IsScottContinuous function

        open IsScottContinuous isScottContinuous public

    apply : (A → A) → A → ℕ → A
    apply f x zero = x 
    apply f x (suc n) = f (apply f x n) 

    module _ (s : ScottContinuous) where

        open ScottContinuous s renaming (function to f ; monotone to m)

        apply⊥Inc : ∀ n → apply f ⊥ n ≲ apply f ⊥ (suc n) 
        apply⊥Inc zero = ⊥isLeast (f ⊥)
        apply⊥Inc (suc n) = monotonicity (apply⊥Inc n)

        apply⊥Increases : ∀ {m n} → m ≤ n → apply f ⊥ m ≲ apply f ⊥ n 
        apply⊥Increases {n = n} z≤n = ⊥isLeast (apply f ⊥ n)
        apply⊥Increases (s≤s m≤n) = monotonicity (apply⊥Increases m≤n) 

        𝕄 : Increasing _≲_
        𝕄 = record { sequence = apply f ⊥ ; isIncreasing = record { increases = apply⊥Increases } } 

        applyPreservesSup : f (sup 𝕄) ≈ sup (m ⊚ 𝕄) 
        applyPreservesSup = continuity 𝕄 

        ↑ : Increasing _≲_ → Increasing _≲_ 
        ↑ f = record 
            { sequence = sequence f ∘ suc 
            ; isIncreasing = record { increases = increases f ∘ s≤s } } 

        supm∘𝕄≈sup↑𝕄 : sup (m ⊚ 𝕄) ≈ sup (↑ 𝕄)
        supm∘𝕄≈sup↑𝕄 = refl
            where open IsEquivalence isEquivalence 

        sup𝕄≲sup↑𝕄 : sup 𝕄 ≲ sup (↑ 𝕄)
        sup𝕄≲sup↑𝕄 = supIsLeastUpperBound 𝕄 (λ n → ≲trans (apply⊥Inc n) (supIsUpperBound (↑ 𝕄) n))

        sup↑𝕄≲sup𝕄 : sup (↑ 𝕄) ≲ sup 𝕄 
        sup↑𝕄≲sup𝕄 = supIsLeastUpperBound (↑ 𝕄) (λ n → supIsUpperBound 𝕄 (suc n)) 

        sup𝕄≈sup↑𝕄 : sup 𝕄 ≈ sup (↑ 𝕄)
        sup𝕄≈sup↑𝕄 = antisym sup𝕄≲sup↑𝕄 sup↑𝕄≲sup𝕄 

        supm∘𝕄≈sup𝕄 : sup (m ⊚ 𝕄) ≈ sup 𝕄
        supm∘𝕄≈sup𝕄 = sym sup𝕄≈sup↑𝕄 
            where open IsEquivalence isEquivalence 

        sup𝕄FixedPoint : f (sup 𝕄) ≈ sup 𝕄 
        sup𝕄FixedPoint = trans applyPreservesSup supm∘𝕄≈sup𝕄
            where open IsEquivalence isEquivalence 

        sup𝕄LFPLemma : ∀ k → f k ≈ k → ∀ n → sequence 𝕄 n ≲ k
        sup𝕄LFPLemma k fp zero = ⊥isLeast k
        sup𝕄LFPLemma k fp (suc n) = ≲trans (monotonicity (sup𝕄LFPLemma k fp n)) (reflexive fp)

        sup𝕄LeastFixedPoint : ∀ k → f k ≈ k → sup 𝕄 ≲ k
        sup𝕄LeastFixedPoint k fp = supIsLeastUpperBound 𝕄 (sup𝕄LFPLemma k fp)

{- 
Adapted from 
    Partiality Revisited: The Partiality Monad as a Quotient Inductive-Inductive Type
    by Thoresten Altenkirch et al.
    https://arxiv.org/pdf/1610.09254.pdf
-}
module Partiality (A : Set) where 

    open import Data.Product
    open import Data.Nat.Properties

    data Partial : Set     
    data _⊑_ : Partial → Partial → Set 

    data Partial where    
        η : A → Partial 
        ⊥ : Partial 
        ⨆ : (s : ℕ → Partial) → (∀ n → s n ⊑ s (suc n)) → Partial

    data _⊑_ where 
        refl⊑ : ∀ {x} → x ⊑ x  
        trans⊑ : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
        ⊥⊑ : ∀ {x} → ⊥ ⊑ x 
        sup⊑ : ∀ s p n → s n ⊑ (⨆ s p)
        lub⊑ : ∀ {x} s p → (∀ n → s n ⊑ x) → (⨆ s p) ⊑ x 

    _≈_ : Partial → Partial → Set 
    x ≈ y = (x ⊑ y) × (y ⊑ x)

    ≈isEquivalence : IsEquivalence _≈_ 
    ≈isEquivalence = record 
        { refl = refl⊑ , refl⊑ 
        ; sym = λ (x⊑y , y⊑x) → y⊑x , x⊑y
        ; trans = λ (x⊑y , y⊑x) (y⊑z , z⊑y) → trans⊑ x⊑y y⊑z , trans⊑ z⊑y y⊑x }

    ⊑isPreorder : IsPreorder _≈_ _⊑_ 
    ⊑isPreorder = record { isEquivalence = ≈isEquivalence ; reflexive = proj₁ ; trans = trans⊑ }

    ⊑isPartialOrder : IsPartialOrder _≈_ _⊑_ 
    ⊑isPartialOrder = record { isPreorder = ⊑isPreorder ; antisym = _,_ } 

    incrOne : (s : Increasing _⊑_) → ∀ n → sequence s n ⊑ sequence s (suc n)
    incrOne s n = increases s (m≤n+m n 1)

    sup : Increasing _⊑_ → Partial 
    sup s = ⨆ (sequence s) (incrOne s) 

    supIsUpperBound : ∀ s n → (sequence s) n ⊑ sup s   
    supIsUpperBound s n = sup⊑ (sequence s) (incrOne s) n

    supIsLeastUpperBound : ∀ {k} s → (∀ n → (sequence s) n ⊑ k) → sup s ⊑ k
    supIsLeastUpperBound s f = lub⊑ (sequence s) (incrOne s) f  

    ⊑isDirected : IsDirected _≈_ _⊑_ 
    ⊑isDirected = record
        { isPartialOrder = ⊑isPartialOrder
        ; sup = sup
        ; supIsUpperBound = supIsUpperBound
        ; supIsLeastUpperBound = supIsLeastUpperBound
        ; ⊥ = ⊥
        ; ⊥isLeast = λ x → ⊥⊑
        }
