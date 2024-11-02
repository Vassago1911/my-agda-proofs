module StandardConstructions.Numbers.NaturalsMultiplicationInjective where 

open import StandardConstructions.AbstractNonsense.IdentityType using (definition-equal ; 🐓🥚 ; cong )
open import StandardConstructions.Numbers.Naturals using ( Nat ; suc ; zero ; add ; mul; suc-inj ) 
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