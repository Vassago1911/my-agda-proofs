module StandardConstructions.Numbers.NaturalsMultiplicationInjective where 

open import StandardConstructions.AbstractNonsense.IdentityType using (definition-equal ; 🐓🥚 ; cong; sym  )
open import StandardConstructions.Numbers.Naturals using ( Nat ; suc ; zero ; add ; mul; suc-inj ; r-add-zero; r-one-neutral; r-zero-absorbs; mul-comm; add-ass; add-pumping; add-comm; nat-add-no-inverses ) 
open import StandardConstructions.Numbers.Integers using ( Int ; nat-int ; int-add; int-mul; int-mul-add-nat-inj; nat-int-inj )

nat-int-add-hom : ( x y : Nat ) -> ( definition-equal ( int-add ( nat-int x ) ( nat-int y ) ) 
                                                  ( nat-int (add x y) ) ) 
nat-int-add-hom x y = 🐓🥚                                                  

nat-int-mul-hom : ( x y : Nat ) -> ( definition-equal ( int-mul ( nat-int x ) ( nat-int y ) ) 
                                                      ( nat-int ( mul x y ) ) ) 
nat-int-mul-hom x y = 🐓🥚

nat-mul-pred-to-int-mul-pred : ( n a b : Nat ) 
    -> ( definition-equal ( mul (suc n) a ) ( mul (suc n) b ) ) 
    -> ( definition-equal ( int-mul (nat-int (suc n) ) (nat-int a) ) ( int-mul ( nat-int (suc n) ) (nat-int b) ) ) 
nat-mul-pred-to-int-mul-pred n a b pred = cong nat-int pred

int-mul-pred-to-eq-pred : ( n a b : Nat ) 
    -> ( definition-equal ( int-mul (nat-int (suc n) ) (nat-int a) ) ( int-mul ( nat-int (suc n) ) (nat-int b) ) )
    -> ( definition-equal (nat-int a) ( nat-int b ) ) 
int-mul-pred-to-eq-pred n a b pred = int-mul-add-nat-inj n (nat-int a) ( nat-int b) pred

int-eq-pred-to-nat-eq-pred : ( a b : Nat ) 
    -> ( definition-equal (nat-int a) ( nat-int b) ) 
    -> ( definition-equal a b ) 
int-eq-pred-to-nat-eq-pred a b  pred = nat-int-inj a b pred

nat-mul-inj : ( n a b : Nat ) 
    -> ( definition-equal ( mul (suc n) a ) ( mul (suc n) b ) ) 
    -> ( definition-equal a b ) 
nat-mul-inj n a b pred = step3
    where step1 = nat-mul-pred-to-int-mul-pred n a b pred 
          step2 = int-mul-pred-to-eq-pred n a b step1 
          step3 = int-eq-pred-to-nat-eq-pred a b step2 

nat-mul-unit-property : ( n a : Nat ) 
    -> ( definition-equal ( mul (suc n) a ) (suc n) ) 
    -> ( definition-equal a (suc zero) ) 
nat-mul-unit-property n a pred = step
    where step1 : ( definition-equal ( mul (suc n) a ) (suc n) ) 
                -> ( definition-equal ( mul (suc n) a ) ( mul (suc n) (suc zero) ) )
          step1 p rewrite ( r-one-neutral {n} ) = p      
          step2 : ( definition-equal ( mul (suc n) a ) ( mul (suc n) (suc zero) ) )
                -> ( definition-equal a (suc zero) ) 
          step2 p = nat-mul-inj n a (suc zero) p
          step = step2 (step1 pred )

nat-mul-unguarded-unit-property : ( n a : Nat ) 
    -> ( definition-equal ( mul n (suc a) ) (suc a) ) 
    -> ( definition-equal n (suc zero ) ) 
nat-mul-unguarded-unit-property zero a   = \ ()  
nat-mul-unguarded-unit-property (suc n) zero pred 
    rewrite ( r-one-neutral {n} ) 
    = pred
nat-mul-unguarded-unit-property (suc n) (suc a) pred 
    rewrite ( mul-comm {n} {suc (suc a) } ) 
    = step4
    where step = suc-inj { (suc (add a (mul (suc (suc a)) n ))) } { (suc a) } pred 
          step1 = suc-inj { (add a (mul (suc (suc a)) n )) } { a } step 
          step2 = nat-add-no-inverses a (mul (suc (suc a)) n ) step1 
          step3 = add-pumping n (add n (mul a n)) step2 
          step4 = cong suc step3 

nat-mul-unit-divisors : ( n m : Nat ) 
    -> ( definition-equal ( mul n m ) (suc zero) ) 
    -> ( definition-equal n (suc zero) ) 
nat-mul-unit-divisors (suc n) zero rewrite ( r-zero-absorbs {n} ) = \ ()    
nat-mul-unit-divisors (suc n) (suc m) pred     
    rewrite ( mul-comm {n} {suc m} ) 
    rewrite ( sym ( add-ass {m} {n} {mul m n} ) ) 
    rewrite ( add-comm {m} {n} ) 
    = addn-pump
    where step = suc-inj pred 
          addmn-pump = add-pumping (add n m) (mul m n) step   
          addn-pump = cong suc (add-pumping n m addmn-pump )
          
          