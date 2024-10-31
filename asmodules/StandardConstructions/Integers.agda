module StandardConstructions.Integers where 

open import StandardConstructions.IdentityType 
    using ( definition-equal; 🐓🥚; cong; sym; extensionality) 
open import StandardConstructions.Maps 
    using ( circ ; id ) 
open import StandardConstructions.Naturals 
    using ( Nat; zero; suc; add; mul; l-add-zero; r-add-zero; add-comm; suc-skip-add; add-ass; mul-comm; r-one-neutral; r-zero-absorbs;
            Pos; p1; one; pos-add; pos-mul; pos-mul3; pos-mul3-lass; pos-add-ass; pos-add-comm; posmul-ass; posmul-comm; pos-mul-lunital; pos-mul-runital ) 

data Int : Set where 
    nat-int : Nat -> Int     
    neg-int : Nat -> Int 

nat-diff-to-int : Nat -> Nat -> Int 
nat-diff-to-int zero zero = nat-int zero
nat-diff-to-int zero (suc m) = neg-int m
nat-diff-to-int (suc n) zero = nat-int (suc n)
nat-diff-to-int (suc n) (suc m) = nat-diff-to-int n m 

minus : Int -> Int 
minus (nat-int zero) = (nat-int zero)
minus (nat-int (suc x)) = (neg-int x)
minus (neg-int x) = (nat-int (suc x))

symm-nat-diff : ( n m : Nat ) -> ( definition-equal ( minus ( nat-diff-to-int n m ) ) ( nat-diff-to-int m n ) ) 
symm-nat-diff zero zero = 🐓🥚
symm-nat-diff zero (suc m) = 🐓🥚
symm-nat-diff (suc n) zero = 🐓🥚
symm-nat-diff (suc n) (suc m) 
    rewrite ( symm-nat-diff n m ) 
    = 🐓🥚

int-suc : Int -> Int 
int-suc (nat-int x) = nat-int (suc x)
int-suc (neg-int zero) = nat-int zero
int-suc (neg-int (suc x)) = neg-int x

suc-int-suc : ( k : Nat ) -> ( definition-equal ( nat-int ( suc k ) ) ( int-suc ( nat-int k ) ) ) 
suc-int-suc z = 🐓🥚

int-pred : Int -> Int 
int-pred (nat-int zero) = neg-int zero
int-pred (nat-int (suc x)) = nat-int x
int-pred (neg-int x) = neg-int ( suc x )

suc-pred : ( k : Int ) -> ( definition-equal ( int-pred ( int-suc k ) ) ( id k ) ) 
suc-pred (nat-int x) = 🐓🥚
suc-pred (neg-int zero) = 🐓🥚
suc-pred (neg-int (suc x)) = 🐓🥚

pred-suc : ( k : Int ) -> ( definition-equal ( int-suc ( int-pred k ) ) ( id k ) ) 
pred-suc (nat-int zero) = 🐓🥚
pred-suc (nat-int (suc x)) = 🐓🥚
pred-suc (neg-int x) = 🐓🥚

minus-self-inverse-pw : ( k : Int ) -> ( definition-equal ( minus ( minus k ) ) k ) 
minus-self-inverse-pw (nat-int zero) = 🐓🥚
minus-self-inverse-pw (nat-int (suc x)) = 🐓🥚
minus-self-inverse-pw (neg-int x) = 🐓🥚
 
minus-suc-pred : ( k : Int ) -> ( definition-equal ( minus ( int-suc k ) ) ( int-pred ( minus k ) ) ) 
minus-suc-pred (nat-int zero) = 🐓🥚
minus-suc-pred (nat-int (suc x)) = 🐓🥚
minus-suc-pred (neg-int zero) = 🐓🥚
minus-suc-pred (neg-int (suc x)) = 🐓🥚

minus-nat : ( x : Nat ) -> ( definition-equal ( minus ( nat-int x ) ) ( int-suc ( neg-int x ) ) ) 
minus-nat zero = 🐓🥚
minus-nat (suc x) = 🐓🥚

minus-neg : ( x : Nat ) -> ( definition-equal ( minus ( neg-int x ) ) ( int-suc ( nat-int x ) ) ) 
minus-neg x = 🐓🥚 

minus-pred-suc : ( k : Int ) -> ( definition-equal ( minus ( int-pred k ) ) ( int-suc ( minus k ) ) ) 
minus-pred-suc (nat-int zero) = 🐓🥚
minus-pred-suc (neg-int zero) = 🐓🥚
minus-pred-suc (neg-int (suc x)) = 🐓🥚 
minus-pred-suc (nat-int (suc x)) 
    rewrite ( suc-int-suc ( suc x ) )
    rewrite ( minus-nat x ) 
    = 🐓🥚

add-int : Int -> Int -> Int 
add-int (nat-int x) (nat-int y) = nat-int (add x y)
add-int (nat-int x) (neg-int y) = nat-diff-to-int x (suc y)
add-int (neg-int x) (nat-int y) = nat-diff-to-int y (suc x)
add-int (neg-int x) (neg-int y) = neg-int (suc (add x y))

add-int-comm : ( n m : Int ) -> ( definition-equal ( add-int n m ) ( add-int m n ) ) 
add-int-comm (nat-int x) (nat-int y) 
    rewrite ( add-comm {y} {x} )     = 🐓🥚
add-int-comm (neg-int x) (neg-int y) 
    rewrite ( add-comm {y} {x} )     = 🐓🥚
add-int-comm (nat-int x) (neg-int y) = 🐓🥚
add-int-comm (neg-int x) (nat-int y) = 🐓🥚

zero-add-int : ( n : Int ) -> ( definition-equal ( add-int (nat-int zero) n ) n ) 
zero-add-int (nat-int x) = 🐓🥚
zero-add-int (neg-int x) = 🐓🥚

add-int-zero : ( n : Int ) -> ( definition-equal ( add-int n ( nat-int zero ) ) n ) 
add-int-zero (nat-int x) 
    rewrite ( r-add-zero {x} ) = 🐓🥚
add-int-zero (neg-int x)       = 🐓🥚

nat-diff-nat-add : ( a b r : Nat ) 
                -> 
                ( definition-equal
                    ( add-int ( nat-diff-to-int a b ) ( nat-int r ) ) 
                    ( nat-diff-to-int ( add a r ) b ) ) 
nat-diff-nat-add zero zero zero = 🐓🥚
nat-diff-nat-add (suc a) zero zero = 🐓🥚
nat-diff-nat-add zero zero (suc r) = 🐓🥚
nat-diff-nat-add (suc a) zero (suc r) = 🐓🥚
nat-diff-nat-add zero (suc b) r = 🐓🥚
nat-diff-nat-add (suc a) (suc b) zero 
    rewrite ( add-int-zero ( nat-diff-to-int a b ) ) 
    rewrite ( r-add-zero {a}) 
    = 🐓🥚
nat-diff-nat-add (suc a) (suc b) (suc r) 
    rewrite (nat-diff-nat-add a b (suc r ) ) 
    = 🐓🥚

nat-diff-neg-add : ( a b r : Nat ) 
                -> 
                ( definition-equal 
                    ( add-int ( nat-diff-to-int a b ) ( neg-int r ) ) 
                    ( nat-diff-to-int a ( suc ( add b r ) ) ) ) 
nat-diff-neg-add zero zero zero = 🐓🥚
nat-diff-neg-add zero zero (suc r) = 🐓🥚
nat-diff-neg-add zero (suc b) r = 🐓🥚
nat-diff-neg-add (suc a) zero r = 🐓🥚
nat-diff-neg-add (suc a) (suc b) r 
    rewrite ( nat-diff-neg-add a b r ) 
    = 🐓🥚

add-nat-diff : ( a b c : Nat ) 
        -> ( definition-equal 
                ( add-int ( nat-int a ) ( nat-diff-to-int b c ) ) 
                ( nat-diff-to-int ( add a b ) c ) ) 
add-nat-diff a b c 
    rewrite ( add-int-comm ( nat-int a ) ( nat-diff-to-int b c ) ) 
    rewrite ( nat-diff-nat-add b c a ) 
    rewrite ( add-comm {b} {a} ) 
    = 🐓🥚

add-neg-diff : ( a b c : Nat ) 
        -> ( definition-equal
                ( add-int ( neg-int a ) ( nat-diff-to-int b c ) ) 
                ( nat-diff-to-int b ( suc ( add a c ) ) ) ) 
add-neg-diff a b c 
    rewrite ( add-int-comm ( neg-int a ) ( nat-diff-to-int b c ) ) 
    rewrite ( nat-diff-neg-add b c a ) 
    rewrite ( add-comm {c} {a} )
    = 🐓🥚                                

add-int-ass : ( k l m : Int ) 
        -> ( definition-equal 
                ( add-int ( add-int k l ) m ) 
                ( add-int k ( add-int l m ) ) )
add-int-ass (nat-int zero) l m 
    rewrite ( zero-add-int l ) 
    rewrite ( zero-add-int ( add-int l m ) ) 
    = 🐓🥚
add-int-ass k (nat-int zero) m 
    rewrite ( add-int-zero k ) 
    rewrite ( zero-add-int m ) 
    = 🐓🥚
add-int-ass k l (nat-int zero) 
    rewrite ( add-int-zero ( add-int k l ) ) 
    rewrite ( add-int-zero l ) 
    = 🐓🥚

add-int-ass (neg-int x)       (neg-int y)       (nat-int (suc z)) 
    rewrite ( add-int-comm ( neg-int x ) ( nat-diff-to-int z y ) ) 
    rewrite ( nat-diff-neg-add z y x ) 
    rewrite ( add-comm {y} {x} ) 
    = 🐓🥚
    
add-int-ass (neg-int x)       (nat-int (suc y)) (nat-int (suc z)) 
    rewrite ( nat-diff-nat-add y x (suc z) )
    = 🐓🥚
    
add-int-ass (nat-int (suc x)) (neg-int y)       (neg-int z)       
    rewrite ( nat-diff-neg-add x y z ) 
    = 🐓🥚
     
add-int-ass (nat-int (suc x)) (neg-int y)       (nat-int (suc z)) 
    rewrite ( nat-diff-nat-add x y (suc z) )
    rewrite ( add-int-comm (nat-int (suc x)) ( nat-diff-to-int z y ) ) 
    rewrite ( nat-diff-nat-add z y ( suc x ) ) 
    rewrite ( suc-skip-add {x} {z} ) 
    rewrite ( suc-skip-add {z} {x} ) 
    rewrite ( add-comm {z} {x} ) 
    = 🐓🥚
    
add-int-ass (nat-int (suc x)) (nat-int (suc y)) (neg-int z)       
    rewrite ( add-int-comm ( nat-int ( suc x ) ) ( nat-diff-to-int y z ) )     
    rewrite ( nat-diff-nat-add y z (suc x) )
    rewrite ( suc-skip-add {x} {y} ) 
    rewrite ( suc-skip-add {y} {x} ) 
    rewrite ( add-comm {y} {x} )
    = 🐓🥚
    
add-int-ass (neg-int x)       (neg-int y)       (neg-int z)       
    rewrite ( suc-skip-add {x} {add y z} ) 
    rewrite ( add-ass {x} {y} {z} ) 
    = 🐓🥚
     
add-int-ass (neg-int x)       (nat-int (suc y)) (neg-int z)       
    rewrite ( add-int-comm (neg-int x) ( nat-diff-to-int y z ) ) 
    rewrite ( nat-diff-neg-add y x z ) 
    rewrite ( nat-diff-neg-add y z x ) 
    rewrite ( add-comm {z} {x} ) 
    = 🐓🥚

add-int-ass (nat-int (suc x)) (nat-int (suc y)) (nat-int (suc z))     
    rewrite ( suc-skip-add {x} {y} )     
    rewrite ( suc-skip-add {x} {add y (suc z)} ) 
    rewrite ( add-ass {x} {y} {suc z} ) 
    = 🐓🥚

add-has-inverses : ( a : Nat ) -> ( definition-equal ( add-int ( nat-int (suc a) ) ( neg-int a ) ) (nat-int zero) ) 
add-has-inverses zero = 🐓🥚 
add-has-inverses (suc a) 
    rewrite ( add-has-inverses a ) 
    = 🐓🥚

data SymmInt : Set where 
    pos : Pos -> SymmInt 
    szero : SymmInt 
    neg : Pos -> SymmInt 

symm-to-asymm-int : SymmInt -> Int 
symm-to-asymm-int (pos (p1 x)) = nat-int (suc x)
symm-to-asymm-int szero = nat-int zero
symm-to-asymm-int (neg (p1 x)) = neg-int x

asymm-to-symm-int : Int -> SymmInt 
asymm-to-symm-int (nat-int zero) = szero
asymm-to-symm-int (nat-int (suc x)) = pos (p1 x)
asymm-to-symm-int (neg-int x) = neg (p1 x)

assi : ( s : SymmInt ) -> ( definition-equal ( asymm-to-symm-int (symm-to-asymm-int s ) ) s ) 
assi (pos (p1 x)) = 🐓🥚
assi szero = 🐓🥚
assi (neg (p1 x)) = 🐓🥚

sasi : ( a : Int ) -> ( definition-equal ( symm-to-asymm-int (asymm-to-symm-int a ) ) a ) 
sasi (nat-int zero) = 🐓🥚
sasi (nat-int (suc x)) = 🐓🥚
sasi (neg-int x) = 🐓🥚

symmint-add : SymmInt -> SymmInt -> SymmInt 
symmint-add x y = asymm-to-symm-int ( add-int ( symm-to-asymm-int x ) ( symm-to-asymm-int y ) ) 

symmint-add-def : ( x y : SymmInt ) 
       -> ( definition-equal 
               ( symmint-add x y ) 
               ( asymm-to-symm-int ( add-int ( symm-to-asymm-int x ) ( symm-to-asymm-int y ) ) ) ) 
symmint-add-def x y = 🐓🥚

symmint-add-zero-neutral : ( x : SymmInt ) -> ( definition-equal ( symmint-add szero x ) x ) 
symmint-add-zero-neutral szero = 🐓🥚
symmint-add-zero-neutral (pos (p1 x)) = 🐓🥚
symmint-add-zero-neutral (neg (p1 x)) = 🐓🥚

symmint-add-comm : ( x y : SymmInt ) 
        -> ( definition-equal 
                ( symmint-add x y ) 
                ( symmint-add y x ) ) 
symmint-add-comm x y 
   rewrite ( symmint-add-def x y ) 
   rewrite ( symmint-add-def y x ) 
   rewrite ( add-int-comm (symm-to-asymm-int y) (symm-to-asymm-int x) )
   = 🐓🥚

symmint-add-ass : ( x y z : SymmInt ) 
            -> ( definition-equal 
                    ( symmint-add ( symmint-add x y ) z ) 
                    ( symmint-add x ( symmint-add y z ) ) ) 
symmint-add-ass x y z 
   rewrite ( symmint-add-def x y ) 
   rewrite ( symmint-add-def y z ) 
   rewrite ( sasi (add-int (symm-to-asymm-int x) (symm-to-asymm-int y)) )
   rewrite ( sasi (add-int (symm-to-asymm-int y) (symm-to-asymm-int z)) ) 
   rewrite ( add-int-ass (symm-to-asymm-int x) (symm-to-asymm-int y) (symm-to-asymm-int z) )
   = 🐓🥚                    

symmint-mul : SymmInt -> SymmInt -> SymmInt 
symmint-mul (pos x) szero = szero
symmint-mul szero   b     = szero
symmint-mul (neg x) szero = szero
symmint-mul (pos x) (pos y) = pos (pos-mul x y)
symmint-mul (pos x) (neg y) = neg (pos-mul x y)
symmint-mul (neg x) (pos y) = neg (pos-mul x y)
symmint-mul (neg x) (neg y) = pos (pos-mul x y)

symmint-mul-zero-absorbs : ( a : SymmInt ) -> ( definition-equal ( symmint-mul a szero ) szero ) 
symmint-mul-zero-absorbs (pos x) = 🐓🥚
symmint-mul-zero-absorbs szero = 🐓🥚
symmint-mul-zero-absorbs (neg x) = 🐓🥚

symmint-mul-one-neutral : ( a : SymmInt ) -> ( definition-equal ( symmint-mul a ( pos (p1 zero) ) ) a ) 
symmint-mul-one-neutral szero = 🐓🥚
symmint-mul-one-neutral (pos (p1 x)) 
    rewrite ( r-one-neutral {x} ) 
    = 🐓🥚
symmint-mul-one-neutral (neg (p1 x)) 
    rewrite ( r-one-neutral {x} ) 
    = 🐓🥚

symmint-mul-comm : ( a b : SymmInt ) 
            -> ( definition-equal 
                    ( symmint-mul a b ) 
                    ( symmint-mul b a ) ) 
symmint-mul-comm (pos x) szero = 🐓🥚
symmint-mul-comm szero (pos x) = 🐓🥚
symmint-mul-comm szero szero = 🐓🥚
symmint-mul-comm szero (neg x) = 🐓🥚
symmint-mul-comm (neg x) szero = 🐓🥚
symmint-mul-comm (pos x) (pos y) 
    rewrite ( posmul-comm x y ) 
    = 🐓🥚
symmint-mul-comm (pos x) (neg y) 
    rewrite ( posmul-comm x y ) 
    = 🐓🥚
symmint-mul-comm (neg x) (pos y) 
    rewrite ( posmul-comm x y ) 
    = 🐓🥚
symmint-mul-comm (neg x) (neg y) 
    rewrite ( posmul-comm x y ) 
    = 🐓🥚

symmint-mul-ass : ( a b c : SymmInt ) 
            -> ( definition-equal 
                    ( symmint-mul ( symmint-mul a b ) c ) 
                    ( symmint-mul a ( symmint-mul b c ) ) ) 
symmint-mul-ass szero b c = 🐓🥚
symmint-mul-ass (pos x) szero (pos y) = 🐓🥚
symmint-mul-ass (pos x) szero szero = 🐓🥚
symmint-mul-ass (pos x) szero (neg y) = 🐓🥚
symmint-mul-ass (pos x) (pos y) szero = 🐓🥚
symmint-mul-ass (pos x) (neg y) szero = 🐓🥚
symmint-mul-ass (neg x) szero c = 🐓🥚
symmint-mul-ass (neg x) (pos y) szero = 🐓🥚
symmint-mul-ass (neg x) (neg y) szero = 🐓🥚
symmint-mul-ass (pos x) (pos y) (pos z) 
    rewrite ( posmul-ass x y z ) 
    = 🐓🥚
symmint-mul-ass (pos x) (pos y) (neg z) 
    rewrite ( posmul-ass x y z ) 
    = 🐓🥚
symmint-mul-ass (pos x) (neg y) (pos z) 
    rewrite ( posmul-ass x y z ) 
    = 🐓🥚
symmint-mul-ass (pos x) (neg y) (neg z) 
    rewrite ( posmul-ass x y z ) 
    = 🐓🥚
symmint-mul-ass (neg x) (pos y) (pos z) 
    rewrite ( posmul-ass x y z ) 
    = 🐓🥚
symmint-mul-ass (neg x) (pos y) (neg z) 
    rewrite ( posmul-ass x y z ) 
    = 🐓🥚
symmint-mul-ass (neg x) (neg y) (pos z) 
    rewrite ( posmul-ass x y z ) 
    = 🐓🥚
symmint-mul-ass (neg x) (neg y) (neg z) 
    rewrite ( posmul-ass x y z ) 
    = 🐓🥚

symmint-mul-negpos : ( x y : Pos ) 
    -> ( definition-equal 
         ( symmint-mul ( neg x ) ( pos y ) ) 
         ( neg ( pos-mul x y ) ) ) 
symmint-mul-negpos x y = 🐓🥚

symmint-mul-posneg : ( x y : Pos ) 
    -> ( definition-equal 
          ( symmint-mul ( pos x ) ( neg y ) ) 
          ( neg ( pos-mul x y ) ) ) 
symmint-mul-posneg x y = 🐓🥚

symmint-mul-pospos : ( x y : Pos ) 
    -> ( definition-equal 
           ( symmint-mul ( pos x ) ( pos y ) ) 
           ( pos ( pos-mul x y ) ) ) 
symmint-mul-pospos x y = 🐓🥚

symmint-mul-negneg : ( x y : Pos ) 
    -> ( definition-equal 
           ( symmint-mul ( neg x ) ( neg y ) ) 
           ( pos ( pos-mul x y ) ) ) 
symmint-mul-negneg x y = 🐓🥚           

symm-minusone : SymmInt 
symm-minusone = neg ( p1 zero ) 

symm-one : SymmInt 
symm-one = pos ( p1 zero ) 

minusone-square : ( definition-equal 
                      ( symmint-mul symm-minusone symm-minusone )
                      symm-one ) 
minusone-square = 🐓🥚 

sign-commute : ( k l : SymmInt ) -> 
    ( definition-equal ( symmint-mul ( symmint-mul symm-minusone k ) l ) 
                       ( symmint-mul symm-minusone ( symmint-mul k l ) ) ) 
sign-commute k l 
   rewrite ( symmint-mul-ass symm-minusone k l ) 
   = 🐓🥚                       

sign-commute-r : ( k l : SymmInt ) -> 
   ( definition-equal ( symmint-mul k ( symmint-mul symm-minusone l ) ) 
                      ( symmint-mul symm-minusone ( symmint-mul k l ) ))
sign-commute-r k l 
  rewrite ( sym ( symmint-mul-ass k symm-minusone l ) ) 
  rewrite ( symmint-mul-comm k symm-minusone ) 
  rewrite ( symmint-mul-ass (neg (p1 zero)) k l ) 
  = 🐓🥚                      

special-sign-commute : ( p : Pos ) -> ( k : SymmInt ) -> 
   ( definition-equal ( symmint-mul ( symmint-mul symm-minusone (pos p) ) k ) 
                      ( symmint-mul (neg p) k ) ) 
special-sign-commute p k 
   rewrite ( pos-mul-lunital p ) 
   = 🐓🥚                      

special-sign-commute-minus : ( p : Pos ) -> ( k : SymmInt ) -> 
   ( definition-equal ( symmint-mul ( symmint-mul symm-minusone (neg p) ) k ) 
                      ( symmint-mul (pos p) k ) ) 
special-sign-commute-minus p k 
   rewrite ( pos-mul-lunital p ) 
   = 🐓🥚

special-sign-commute-r : ( k : SymmInt ) -> ( p : Pos ) ->
   ( definition-equal ( symmint-mul k ( symmint-mul symm-minusone (pos p) ) )
                      ( symmint-mul k (neg p) ) ) 
special-sign-commute-r k p 
    rewrite (pos-mul-lunital p ) 
    = 🐓🥚

special-sign-commute-minus-r : ( k : SymmInt ) -> ( p : Pos ) -> 
   ( definition-equal ( symmint-mul k ( symmint-mul symm-minusone (neg p) ) ) 
                      ( symmint-mul k ( pos p ) ) ) 
special-sign-commute-minus-r k p 
    rewrite (pos-mul-lunital p ) 
    = 🐓🥚                                                

pos-add-hom : ( p q : Pos ) 
   -> ( definition-equal 
           ( symmint-add ( pos p ) ( pos q ) ) 
           ( pos ( pos-add p q ) ) ) 
pos-add-hom (p1 x) (p1 y) 
  rewrite ( symmint-add-def (pos (p1 x)) (pos (p1 y)) ) 
  rewrite ( suc-skip-add {x} {y} ) 
  = 🐓🥚           
          


mulint : Int -> Int -> Int 
mulint k l = symm-to-asymm-int ( symmint-mul ( asymm-to-symm-int k ) ( asymm-to-symm-int l ) )

mulhom-sas : ( a b : SymmInt ) 
    -> ( definition-equal 
            ( mulint ( symm-to-asymm-int a ) ( symm-to-asymm-int b ) ) 
            ( symm-to-asymm-int ( symmint-mul a b ) ) 
            ) 
mulhom-sas szero b = 🐓🥚
mulhom-sas (pos (p1 x)) (pos (p1 y)) = 🐓🥚
mulhom-sas (pos (p1 x)) szero = 🐓🥚
mulhom-sas (pos (p1 x)) (neg (p1 y)) = 🐓🥚
mulhom-sas (neg (p1 x)) (pos (p1 y)) = 🐓🥚
mulhom-sas (neg (p1 x)) szero = 🐓🥚
mulhom-sas (neg (p1 x)) (neg (p1 y)) = 🐓🥚

mulint-comm : ( n m : Int ) 
        -> ( definition-equal 
                ( mulint n m ) 
                ( mulint m n ) ) 
mulint-comm n m 
    rewrite ( sasi n ) 
    rewrite ( sasi m ) 
    rewrite ( symmint-mul-comm (asymm-to-symm-int n) (asymm-to-symm-int m ) ) 
    = 🐓🥚

mulint-ass : ( k l m : Int ) 
        -> ( definition-equal 
                ( mulint ( mulint k l ) m ) 
                ( mulint k ( mulint l m ) ) ) 
mulint-ass k l m 
    rewrite ( sasi k )
    rewrite ( assi (symmint-mul (asymm-to-symm-int l) (asymm-to-symm-int m)))
    rewrite ( assi (symmint-mul (asymm-to-symm-int k) (asymm-to-symm-int l)))
    rewrite ( symmint-mul-ass (asymm-to-symm-int k) (asymm-to-symm-int l) (asymm-to-symm-int m) )
    = 🐓🥚

oneint : Int 
oneint = nat-int (suc zero)

mulint-zero-absorbs : ( n : Int ) -> ( definition-equal ( mulint (nat-int zero) n ) (nat-int zero) ) 
mulint-zero-absorbs n = 🐓🥚

mulint-one-neutral : ( n : Int ) -> ( definition-equal ( mulint oneint n ) n ) 
mulint-one-neutral n 
    rewrite ( sasi n ) 
    rewrite ( symmint-mul-comm (pos (p1 zero)) (asymm-to-symm-int n))
    rewrite ( symmint-mul-one-neutral (asymm-to-symm-int n) )
    rewrite ( sasi n  )
    = 🐓🥚    