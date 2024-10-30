module StandardConstructions.Integers where 

open import StandardConstructions.IdentityType using ( definition-equal; 🐓🥚; cong; sym; extensionality) 
open import StandardConstructions.Maps using ( circ ; id ) 
open import StandardConstructions.Naturals using ( Nat; zero; suc; add; mul; r-add-zero; add-comm; suc-skip-add; add-ass ) 

data Int : Set where 
    int-p1 : Nat -> Int 
    int-zero : Int 
    int-m1 : Nat -> Int 

minus : Int -> Int 
minus (int-p1 x) = int-m1 x
minus int-zero = int-zero
minus (int-m1 x) = int-p1 x

int-suc : Int -> Int 
int-suc (int-p1 x) = int-p1 (suc x )
int-suc int-zero = int-p1 zero
int-suc (int-m1 zero) = int-zero 
int-suc (int-m1 (suc x)) = int-m1 x

suc-int-suc : ( k : Nat ) -> ( definition-equal ( int-p1 ( suc k ) ) ( int-suc ( int-p1 k ) ) ) 
suc-int-suc zero = 🐓🥚
suc-int-suc (suc k) = 🐓🥚

int-pred : Int -> Int 
int-pred (int-p1 zero) = int-zero
int-pred (int-p1 (suc x)) = int-p1 x
int-pred int-zero = int-m1 zero 
int-pred (int-m1 x) = int-m1 ( suc x )

suc-pred : ( k : Int ) -> ( definition-equal ( int-pred ( int-suc k ) ) ( id k ) ) 
suc-pred (int-p1 x) = 🐓🥚 
suc-pred (int-zero) = 🐓🥚
suc-pred (int-m1 zero) = 🐓🥚 
suc-pred (int-m1 (suc x)) = 🐓🥚

pred-suc : ( k : Int ) -> ( definition-equal ( int-suc ( int-pred k ) ) ( id k ) ) 
pred-suc (int-p1 zero) = 🐓🥚
pred-suc (int-p1 (suc x)) = 🐓🥚
pred-suc (int-zero) = 🐓🥚
pred-suc (int-m1 x) = 🐓🥚

suc-pred-id : ( definition-equal ( circ int-pred int-suc ) id ) 
suc-pred-id = extensionality suc-pred

pred-suc-id : ( definition-equal ( circ int-suc int-pred ) id ) 
pred-suc-id = extensionality pred-suc

minus-self-inverse-pw : ( k : Int ) -> ( definition-equal ( minus ( minus k ) ) k ) 
minus-self-inverse-pw (int-p1 x) = 🐓🥚
minus-self-inverse-pw int-zero = 🐓🥚
minus-self-inverse-pw (int-m1 x) = 🐓🥚
 
minus-self-inverse : ( definition-equal ( circ minus minus ) id ) 
minus-self-inverse = extensionality minus-self-inverse-pw

minus-suc-pred : ( k : Int ) -> ( definition-equal ( minus ( int-suc k ) ) ( int-pred ( minus k ) ) ) 
minus-suc-pred (int-p1 x) = 🐓🥚
minus-suc-pred int-zero = 🐓🥚
minus-suc-pred (int-m1 zero) = 🐓🥚 
minus-suc-pred (int-m1 (suc x)) = 🐓🥚

minus-pred-suc : ( k : Int ) -> ( definition-equal ( minus ( int-pred k ) ) ( int-suc ( minus k ) ) ) 
minus-pred-suc (int-p1 zero) = 🐓🥚
minus-pred-suc (int-p1 (suc x)) = 🐓🥚
minus-pred-suc int-zero = 🐓🥚 
minus-pred-suc (int-m1 x) = 🐓🥚

minus-suc-is-pred-minus : ( definition-equal ( circ minus int-suc ) ( circ int-pred minus ) ) 
minus-suc-is-pred-minus = extensionality minus-suc-pred

minus-pred-is-suc-minus : ( definition-equal ( circ minus int-pred ) ( circ int-suc minus ) ) 
minus-pred-is-suc-minus = extensionality minus-pred-suc

add-int : Int -> Int -> Int 
add-int (int-m1 zero) (int-m1 y)          = int-m1 ( suc y ) 
add-int int-zero (int-m1 x)               = int-m1 x
add-int (int-m1 x) int-zero               = int-m1 x
add-int (int-m1 (suc x)) (int-p1 zero)    = int-m1 x 
add-int (int-p1 zero) (int-m1 (suc y))    = int-m1 y
add-int int-zero int-zero                 = int-zero 
add-int (int-m1 zero) (int-p1 zero)       = int-zero
add-int (int-p1 zero) (int-m1 zero)       = int-zero
add-int int-zero (int-p1 x)               = int-p1 x
add-int (int-p1 x) int-zero               = int-p1 x
add-int (int-p1 (suc x)) (int-m1 zero)    = int-p1 x
add-int (int-m1 zero) (int-p1 (suc y))    = int-p1 y  
add-int (int-p1 zero) (int-p1 y)          = int-p1 ( suc y )
add-int (int-p1 (suc x)) (int-p1 y)       = add-int ( int-p1 x ) ( int-p1 (suc y ) )
add-int (int-m1 (suc x)) (int-m1 y)       = add-int ( int-m1 x ) ( int-m1 ( suc y ) )
add-int (int-p1 (suc x)) (int-m1 (suc y)) = add-int ( int-p1 x ) ( int-m1 y )  
add-int (int-m1 (suc x)) (int-p1 (suc y)) = add-int ( int-m1 x ) ( int-p1 y )
