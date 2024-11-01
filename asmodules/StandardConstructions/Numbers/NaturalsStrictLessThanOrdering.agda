module StandardConstructions.Numbers.NaturalsStrictLessThanOrdering where 

open import StandardConstructions.AbstractNonsense.IdentityType using ( definition-equal; 🐓🥚; cong ) 
open import StandardConstructions.AbstractNonsense.Not using ( 🐷🛸 ) 
open import StandardConstructions.AbstractNonsense.Sum using ( Sum; injl; injr )
open import StandardConstructions.Numbers.Naturals using ( Nat ; suc ; zero ) 

data less-than : Nat -> Nat -> Set where 
    gt-zero : { k : Nat } -> ( less-than zero (suc k) ) 
    gt-succ : { k l : Nat } -> ( less-than k l ) -> ( less-than ( suc k ) ( suc l ) )

gt-succ-inv : { k l : Nat } -> ( less-than ( suc k ) ( suc l ) ) -> ( less-than k l ) 
gt-succ-inv (gt-succ predkl) = predkl

lt-trans : { k l m : Nat } -> ( less-than k l ) -> ( less-than l m ) -> ( less-than k m ) 
lt-trans {zero} {suc l} {suc m} predkl predlm = gt-zero 
lt-trans {suc k} {suc l} {suc m} (gt-succ predkl) (gt-succ predlm) = gt-succ ( lt-trans predkl predlm )

lt-irrefl : { k : Nat } -> ( less-than k k ) -> 🐷🛸
lt-irrefl {suc k} = λ x → lt-irrefl { k } ( gt-succ-inv x  )

lt-antisymm : { k l : Nat } -> ( less-than k l ) -> ( less-than l k ) -> 🐷🛸
lt-antisymm {suc k} {suc l} (gt-succ predkl) (gt-succ predlk) = lt-antisymm {k} {l} predkl predlk

trichotomy-step : { k l : Nat } 
               -> Sum ( Sum ( less-than k l ) ( definition-equal k l ) ) ( less-than l k ) 
               -> Sum ( Sum ( less-than (suc k) (suc l) ) ( definition-equal (suc k) (suc l) ) ) ( less-than (suc l) (suc k) )
trichotomy-step (injl (injl x)) = injl (injl (gt-succ x))
trichotomy-step (injl (injr x)) = injl (injr ( cong suc x ))
trichotomy-step (injr x) = injr ( gt-succ x )

trichotomy : { k l : Nat } 
          -> Sum ( Sum ( less-than k l ) ( definition-equal k l ) ) ( less-than l k ) 
trichotomy {zero} {zero} = injl (injr 🐓🥚)
trichotomy {zero} {suc l} = injl ( injl gt-zero )  
trichotomy {suc k} {zero} = injr gt-zero 
trichotomy {suc k} {suc l} = trichotomy-step ( trichotomy { k } { l } )

