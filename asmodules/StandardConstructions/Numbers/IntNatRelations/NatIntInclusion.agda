module StandardConstructions.Numbers.IntNatRelations.NatIntInclusion where 

open import StandardConstructions.AbstractNonsense.IdentityType using ( definition-equal; 🐓🥚 ) 
open import StandardConstructions.Numbers.Naturals using ( Nat ; zero ; suc ; add ; mul; r-zero-absorbs; nat-mul-no-zero-div )
open import StandardConstructions.Numbers.NaturalsStrictLessThanOrdering using ( less-than ) 
open import StandardConstructions.Numbers.Integers using ( Int ; nat-int ; neg-int ; int-add ; int-add-inverse; int-mul; int-add-inverse-zero )

nat-add-completion : Nat -> Int 
nat-add-completion x = nat-int x 

int-abs-to-nat : Int -> Nat 
int-abs-to-nat (nat-int x) = x
int-abs-to-nat (neg-int x) = suc x

nat-int-embeds : ( n : Nat ) -> ( definition-equal ( int-abs-to-nat ( nat-add-completion n ) ) n ) 
nat-int-embeds n = 🐓🥚

int-abs-zero-is-zero : ( p : Int ) 
            -> ( definition-equal ( int-abs-to-nat p ) zero ) 
            -> ( definition-equal p (nat-int zero) ) 
int-abs-zero-is-zero (nat-int zero) pred = 🐓🥚

int-abs-mul-is-mul-abs : ( p q : Int ) 
            -> ( definition-equal 
                       ( mul ( int-abs-to-nat p ) ( int-abs-to-nat q ) ) 
                       ( int-abs-to-nat ( int-mul p q ) ) ) 
int-abs-mul-is-mul-abs (nat-int x) (nat-int x₁) = 🐓🥚
int-abs-mul-is-mul-abs (nat-int zero) (neg-int zero) = 🐓🥚
int-abs-mul-is-mul-abs (nat-int (suc x)) (neg-int zero) = 🐓🥚
int-abs-mul-is-mul-abs (nat-int zero) (neg-int (suc y)) = 🐓🥚
int-abs-mul-is-mul-abs (nat-int (suc x)) (neg-int (suc y)) = 🐓🥚
int-abs-mul-is-mul-abs (neg-int zero) (nat-int zero) = 🐓🥚
int-abs-mul-is-mul-abs (neg-int zero) (nat-int (suc x)) = 🐓🥚
int-abs-mul-is-mul-abs (neg-int zero) (neg-int x) = 🐓🥚
int-abs-mul-is-mul-abs (neg-int (suc x)) (nat-int (suc y)) = 🐓🥚
int-abs-mul-is-mul-abs (neg-int (suc x)) (neg-int x₁) = 🐓🥚            
int-abs-mul-is-mul-abs (neg-int (suc x)) (nat-int zero) 
    rewrite ( r-zero-absorbs {x} )
    rewrite ( int-add-inverse-zero )     
    = 🐓🥚
