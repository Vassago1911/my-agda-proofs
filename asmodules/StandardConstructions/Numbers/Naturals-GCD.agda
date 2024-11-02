module StandardConstructions.Numbers.Naturals-GCD where 

open import StandardConstructions.AbstractNonsense.IdentityType using ( definition-equal; 🐓🥚; cong; sym; trans  ) 
open import StandardConstructions.Numbers.Naturals using ( Nat ; zero ; suc ; add ; mul; r-add-zero ; mul-ass ) 

record divides-type  ( m n : Nat ) : Set where 
    constructor divides 
    field quotient : Nat 
          equality : definition-equal n ( mul quotient m ) 
open divides-type using (quotient) public 

divides-type-reflexive : ( n : Nat ) -> ( divides-type n n ) 
divides-type-reflexive n = divides ((suc zero)) (sym ( r-add-zero {n} ))

divides-type-transitive : ( k l m : Nat ) -> ( divides-type k l ) -> ( divides-type l m ) -> ( divides-type k m ) 
divides-type-transitive k l m (divides quotientkl equalitykl) (divides quotientlm equalitylm) = divides ((mul quotientlm quotientkl)) step1
    where congeqkl = ( cong ( \ z -> mul quotientlm z ) equalitykl )          
          step = trans equalitylm congeqkl
          lass = sym ( mul-ass {quotientlm} {quotientkl} {k} )
          step1 = trans step lass 

divides-type-antisymm : ( k l : Nat ) -> ( divides-type k l ) -> ( divides-type l k ) -> ( definition-equal k l ) 
divides-type-antisymm zero zero predkl predlk = 🐓🥚
divides-type-antisymm zero l (divides qkl eqkl) (divides qlk eqlk) = {!   !} 
divides-type-antisymm k zero (divides qkl eqkl) (divides qlk eqlk) = {!   !} 
divides-type-antisymm (suc k) (suc l) (divides qkl eqkl) (divides qlk eqlk) = {!   !} 