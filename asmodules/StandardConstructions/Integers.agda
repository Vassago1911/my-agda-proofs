module StandardConstructions.Integers where 

open import StandardConstructions.IdentityType 
    using ( definition-equal; 🐓🥚; cong; sym; extensionality) 
open import StandardConstructions.Maps 
    using ( circ ; id ) 
open import StandardConstructions.Naturals 
    using ( Nat; zero; suc; add; mul; l-add-zero; r-add-zero; add-comm; suc-skip-add; add-ass ) 

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
symm-nat-diff (suc n) (suc m) = symm-nat-diff n m

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
    = minus-nat x

add-int : Int -> Int -> Int 
add-int (nat-int x) (nat-int y) = nat-int (add x y)
add-int (nat-int x) (neg-int y) = nat-diff-to-int x (suc y)
add-int (neg-int x) (nat-int y) = nat-diff-to-int y (suc x)
add-int (neg-int x) (neg-int y) = neg-int (suc (add x y))

add-int-comm : ( n m : Int ) -> ( definition-equal ( add-int n m ) ( add-int m n ) ) 
add-int-comm (nat-int x) (nat-int y) = cong nat-int ( add-comm {x} {y} ) 
add-int-comm (neg-int x) (neg-int y) = cong neg-int (cong suc (add-comm {x} {y}))
add-int-comm (nat-int x) (neg-int y) = 🐓🥚
add-int-comm (neg-int x) (nat-int y) = 🐓🥚

zero-add-int : ( n : Int ) -> ( definition-equal ( add-int (nat-int zero) n ) n ) 
zero-add-int (nat-int x) = 🐓🥚
zero-add-int (neg-int x) = 🐓🥚

add-int-zero : ( n : Int ) -> ( definition-equal ( add-int n ( nat-int zero ) ) n ) 
add-int-zero (nat-int x) = cong nat-int (r-add-zero {x})
add-int-zero (neg-int x) = 🐓🥚

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
nat-diff-nat-add (suc a) (suc b) (suc r) = nat-diff-nat-add a b (suc r)

nat-diff-neg-add : ( a b r : Nat ) 
                -> 
                ( definition-equal 
                    ( add-int ( nat-diff-to-int a b ) ( neg-int r ) ) 
                    ( nat-diff-to-int a ( suc ( add b r ) ) ) ) 
nat-diff-neg-add zero zero zero = 🐓🥚
nat-diff-neg-add zero zero (suc r) = 🐓🥚
nat-diff-neg-add zero (suc b) r = 🐓🥚
nat-diff-neg-add (suc a) zero r = 🐓🥚
nat-diff-neg-add (suc a) (suc b) r = nat-diff-neg-add a b r

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