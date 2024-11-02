module StandardConstructions.Numbers.Naturals-GCD where 

open import StandardConstructions.AbstractNonsense.IdentityType using ( definition-equal; 🐓🥚; cong; sym; trans  ) 
open import StandardConstructions.Numbers.Naturals using ( Nat ; zero ; suc ; add ; mul; r-add-zero ; mul-ass; mul-comm;  r-zero-absorbs ; suc-inj; r-one-neutral) 
open import StandardConstructions.Numbers.NaturalsMultiplicationInjective using ( nat-mul-unit-property; nat-mul-unit-divisors; nat-mul-unguarded-unit-property )

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
divides-type-antisymm zero l (divides zero eqkl) (divides zero eqlk) = sym eqkl
divides-type-antisymm zero l (divides zero eqkl) (divides (suc qlk) eqlk) = sym eqkl
divides-type-antisymm zero l (divides (suc qkl) eqkl) (divides qlk eqlk) 
    rewrite ( r-zero-absorbs {qkl} ) 
    = sym eqkl 
divides-type-antisymm k zero (divides qkl eqkl) (divides qlk eqlk) 
    rewrite ( r-zero-absorbs {qlk} ) 
    = eqlk   
divides-type-antisymm (suc k) (suc l) (divides qkl eqkl) (divides qlk eqlk) = res 
    where conglk = cong ( \ z -> mul qkl z ) eqlk 
          step = trans eqkl conglk 
          lass = mul-ass {qkl} {qlk} {suc l} 
          step1 : definition-equal (mul (mul qkl qlk) (suc l)) (suc l)
          step1 = sym ( trans step (sym lass) )   
          step2 : definition-equal (mul qkl qlk) (suc zero)           
          step2 = nat-mul-unguarded-unit-property (mul qkl qlk) l step1 
          step3 : ( definition-equal qkl (suc zero ) ) 
          step3 = nat-mul-unit-divisors qkl qlk step2 
          twist : (definition-equal (mul qkl qlk) (mul qlk qkl) ) 
          twist = mul-comm {qkl} {qlk} 
          step2-t : definition-equal ( mul qlk qkl ) (suc zero) 
          step2-t = trans (sym twist) step2 
          step4 : ( definition-equal qlk ( suc zero) ) 
          step4 = nat-mul-unit-divisors qlk qkl step2-t
          step5 : ( definition-equal ( mul qkl (suc k) ) (suc k) ) 
          step5 
            rewrite ( step3 )
            rewrite ( r-add-zero {k} ) 
            = 🐓🥚
          res = sym ( trans eqkl step5 )

divides-type-one-div-all : ( n : Nat ) -> ( divides-type (suc zero) n ) 
divides-type-one-div-all n = divides n (sym ( r-one-neutral {n} ))

divides-type-all-div-zero : ( n : Nat ) -> ( divides-type n zero ) 
divides-type-all-div-zero n = divides zero 🐓🥚 

divides-type-only-zero-div-n : ( n : Nat ) -> ( divides-type zero n ) -> ( definition-equal n zero ) 
divides-type-only-zero-div-n n (divides q eq) 
    rewrite (r-zero-absorbs {q} ) = eq

