module StandardConstructions.Numbers.Naturals-GCD where 

open import StandardConstructions.AbstractNonsense.IdentityType using ( definition-equal; 🐓🥚; cong; cong2; sym; trans  ) 
open import StandardConstructions.AbstractNonsense.Product using ( Product; _,_ ; pr1 ; pr2 ; twist-map )
open import StandardConstructions.Numbers.Naturals using ( Nat ; zero ; suc ; add ; mul; r-add-zero ; mul-ass; mul-comm;  r-zero-absorbs ; suc-inj; r-one-neutral; rdist-mul ) 
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

divides-type-only-one-div-one : ( n : Nat ) -> ( divides-type n (suc zero) ) -> ( definition-equal n (suc zero) ) 
divides-type-only-one-div-one zero (divides quotient equality) 
    rewrite ( r-zero-absorbs {quotient} ) = sym equality
divides-type-only-one-div-one (suc n) pred = divansymm
    where allone = divides-type-one-div-all (suc n) 
          divansymm = divides-type-antisymm (suc n) (suc zero) pred allone 

divides-type-add : ( n p q : Nat ) 
                -> ( divides-type n p ) -> ( divides-type n q ) 
                -> ( divides-type n ( add p q ) ) 
divides-type-add n p q (divides qnp eqnp) (divides qnq eqnq) = divides ((add qnp qnq)) step2                
    where step = cong2 add eqnp eqnq 
          step1 = rdist-mul { qnp } { qnq } { n } 
          step2 = trans step step1 

divides-type-mul : ( n m p q : Nat ) 
                -> ( divides-type n m ) -> ( divides-type p q ) 
                -> ( divides-type ( mul n p ) ( mul m q ) ) 
divides-type-mul n m p q (divides qnm eqnm) (divides qpq eqpq)     
    = divides (mul qpq qnm) res
    where step1 = cong2 mul eqpq eqnm                 
          sstep1 = mul-comm {m} {q} 
          step2 : definition-equal (mul m q) (mul (mul qpq p) (mul qnm n))
          step2 = trans sstep1 step1 
          step3 : definition-equal ( mul ( mul qpq p ) ( mul qnm n ) ) (mul (mul qpq qnm) (mul n p))
          step3 
            rewrite ( sym ( mul-ass {mul qpq p} {qnm} {n} ) ) 
            rewrite ( mul-ass {qpq} {p} {qnm} ) 
            rewrite ( mul-comm {p} {qnm} ) 
            rewrite ( sym ( mul-ass {qpq} {qnm} {p} ) ) 
            rewrite ( mul-ass {mul qpq qnm} {p} {n} ) 
            rewrite ( mul-comm {p} {n} ) 
            = 🐓🥚
          res = trans step2 step3 

divides-type-eckmann-hilton : ( a b c d : Nat ) 
             -> 
             ( definition-equal
                ( mul ( mul a b ) ( mul c d ) )                
                ( mul ( mul a c ) ( mul b d ) ) )
divides-type-eckmann-hilton a b c d 
   rewrite ( mul-ass {a} {b} {mul c d} ) 
   rewrite ( mul-ass {a} {c} {mul b d} )    
   rewrite ( sym ( mul-ass {b} {c} {d} ) ) 
   rewrite ( sym ( mul-ass {c} {b} {d} ) ) 
   rewrite ( mul-comm {c} {b} ) 
   = 🐓🥚 

divides-type-add-mix : ( d e m q n p : Nat ) 
    -> ( divides-type e p ) 
    -> ( divides-type e q ) 
    -> ( divides-type d m ) 
    -> ( divides-type d n ) 
    -> ( divides-type ( mul d e ) ( add ( mul m q ) ( mul n p ) )  )
divides-type-add-mix d e m q n p (divides qpe qqpe) (divides qqe qqqe) (divides qmd qqmd) (divides qnd qqnd) = divides ((add (mul qmd qqe) (mul qnd qpe))) step6  
         where step01 = cong2 mul qqmd qqqe 
               step02 = cong2 mul qqnd qqpe 
               step03 = divides-type-eckmann-hilton qnd d qpe e 
               step04 = divides-type-eckmann-hilton qmd d qqe e 
               step3 = trans step02 step03 
               step4 = trans step01 step04 
               step5 = cong2 add step4 step3 
               step05 = rdist-mul {(mul qmd qqe)} {(mul qnd qpe)} {mul d e} 
               step6 = trans step5 step05 


record GCD ( m n gcd : Nat ) : Set where 
    constructor is 
    field
        commondivisor : Product ( divides-type gcd m ) ( divides-type gcd n )
        greatest : ( d : Nat ) -> ( Product ( divides-type d m ) ( divides-type d n) ) -> ( divides-type d gcd )
open GCD public 

gcd-unique : ( m n d1 d2 : Nat ) -> ( GCD m n d1 ) -> ( GCD m n d2 ) -> ( definition-equal d1 d2 )
gcd-unique m n d1 d2 (is commondivisord1 greatestd1) (is commondivisord2 greatestd2) = myrefl
    where step21 = greatestd2 d1 commondivisord1
          step12 = greatestd1 d2 commondivisord2
          myrefl = divides-type-antisymm d1 d2 step21 step12 

gcd-refl : ( n : Nat ) -> ( GCD n n n ) 
gcd-refl zero = is ((divides-type-reflexive zero) , (divides-type-reflexive zero)) ( \ d _ -> divides-type-all-div-zero d )
gcd-refl (suc n) = is (divides-type-reflexive (suc n) , divides-type-reflexive (suc n)) ( \ d p -> pr1 p )

gcd-symm : ( n m : Nat ) -> { d : Nat } -> ( GCD n m d ) -> ( GCD m n d ) 
gcd-symm n m {d} (is (dn , dm) grd) = is (dm , dn) \ dd -> twist-map ( grd dd )

gcd-rat-add-gcd-max-preserve :  ( m n d p q e : Nat ) 
   -> ( (dparam : Nat) -> ( Product (divides-type dparam p) (divides-type dparam q) ) -> ( divides-type dparam e ) )
   -> ( (eparam : Nat) -> ( Product (divides-type eparam m) (divides-type eparam n) ) -> ( divides-type eparam d ) )
   -> ( ( dparam : Nat ) -> 
        ( Product 
            (divides-type dparam (add (mul m q) (mul n p)))
            (divides-type dparam (mul n q)) )
        -> divides-type dparam (mul d e) )
gcd-rat-add-gcd-max-preserve m n d p q e maxpredpq-e maxpredmn-d dparam (divmqaddnp , divnq ) = {!   !}        



gcd-rat-add : ( m n d p q e : Nat ) 
           -> ( GCD m n d ) -> ( GCD p q e ) 
           -> ( GCD ( add (mul m q) (mul n p) ) ( mul n q ) ( mul d e ) )
gcd-rat-add m n d p q e (is dmn gdmn ) (is dpq gdpq ) = is (step2 , step1) \ dparam -> \ z -> {!  !}
    where edp = pr1 dpq
          ddm = pr1 dmn 
          edq = pr2 dpq 
          ddn = pr2 dmn      
          step1 = divides-type-mul d n e q ddn edq 
          step2 = divides-type-add-mix d e m q n p edp edq ddm ddn 