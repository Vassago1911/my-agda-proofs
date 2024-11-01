module StandardConstructions.Numbers.NaturalsLessThanOrEqualOrdering where 

open import StandardConstructions.AbstractNonsense.IdentityType using ( definition-equal; 🐓🥚; cong ) 
open import StandardConstructions.AbstractNonsense.Sum using ( Sum; injl; injr )
open import StandardConstructions.Numbers.Naturals using ( Nat ; suc ; zero ) 

data lteq : Nat -> Nat -> Set where 
    gteq-zero : { k : Nat } -> ( lteq zero k ) 
    gteq-succ : { k l : Nat } -> ( lteq k l ) -> ( lteq ( suc k ) ( suc l ) )

gt-succ-inv : { k l : Nat } -> ( lteq ( suc k ) ( suc l ) ) -> ( lteq k l ) 
gt-succ-inv (gteq-succ predkl) = predkl

lteq-trans : { k l m : Nat } -> ( lteq k l ) -> ( lteq l m ) -> ( lteq k m ) 
lteq-trans {zero} {zero} {zero} predkl predlm = gteq-zero
lteq-trans {zero} {zero} {suc m} predkl predlm = gteq-zero
lteq-trans {zero} {suc l} {m} predkl predlm = gteq-zero
lteq-trans {suc k} {suc l} {suc m} (gteq-succ predkl) (gteq-succ predlm) = gteq-succ (lteq-trans predkl predlm)

lteq-antisymm : { k l : Nat } -> ( lteq k l ) -> ( lteq l k ) -> ( definition-equal k l )
lteq-antisymm {zero} {zero} gteq-zero gteq-zero = 🐓🥚
lteq-antisymm {suc k} {suc l} (gteq-succ predkl) (gteq-succ predlk) = cong suc (lteq-antisymm predkl predlk)

lteq-refl : { k : Nat } -> ( lteq k k ) 
lteq-refl {zero} = gteq-zero
lteq-refl {suc k} = gteq-succ (lteq-refl {k}) 

lteq-trichotomy-step : { k l : Nat } 
                   -> Sum ( lteq k l ) ( lteq l k ) 
                   -> Sum ( lteq (suc k) (suc l) ) ( lteq (suc l) (suc k) )
lteq-trichotomy-step (injl x) = injl ( gteq-succ x )
lteq-trichotomy-step (injr x) = injr ( gteq-succ x )

lteq-trichotomy : { k l : Nat } 
               -> Sum ( lteq k l ) ( lteq l k ) 
lteq-trichotomy {zero} {zero} = injl gteq-zero
lteq-trichotomy {zero} {suc l} = injl gteq-zero  
lteq-trichotomy {suc k} {zero} = injr gteq-zero 
lteq-trichotomy {suc k} {suc l} = lteq-trichotomy-step (lteq-trichotomy {k} {l})