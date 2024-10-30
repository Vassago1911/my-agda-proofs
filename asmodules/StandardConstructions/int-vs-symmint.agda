module StandardConstructions.int-vs-symmint where 

open import StandardConstructions.IdentityType 
    using ( definition-equal; 🐓🥚; cong; sym; extensionality) 

data Nat : Set where 
    zero : Nat 
    suc : Nat -> Nat 

data Pos : Set where 
    p1 : Nat -> Pos 

pos-to-nat-pred : Pos -> Nat 
pos-to-nat-pred (p1 x) = x 

nat-to-pos-suc : Nat -> Pos 
nat-to-pos-suc x = p1 x 

npn-iso : ( n : Nat ) -> ( definition-equal ( pos-to-nat-pred ( nat-to-pos-suc n ) ) n ) 
npn-iso zero = 🐓🥚
npn-iso (suc n) = 🐓🥚

pnp-iso : ( p : Pos ) -> ( definition-equal ( nat-to-pos-suc ( pos-to-nat-pred p ) ) p ) 
pnp-iso (p1 x) = 🐓🥚

data NonZeroInt : Set where 
    posint : Pos -> NonZeroInt  -- ( n > 0 )
    negint : Pos -> NonZeroInt  -- ( n < 0 )  

data Int : Set where 
    nzeroint : NonZeroInt -> Int -- ( n <> 0 ) 
    zero-int :               Int -- ( n == 0 )  

data AsymmInt : Set where 
    natint : Nat -> AsymmInt -- ( n >= 0 ) 
    negint : Nat -> AsymmInt -- ( -(n+1) < 0 )

symm-to-asymm-int : Int -> AsymmInt
symm-to-asymm-int (nzeroint (posint (p1 x))) = natint (suc x)
symm-to-asymm-int (nzeroint (negint (p1 x))) = negint x
symm-to-asymm-int zero-int = natint zero

asymm-to-symm-int : AsymmInt -> Int 
asymm-to-symm-int (natint zero) = zero-int
asymm-to-symm-int (natint (suc x)) = nzeroint (posint (p1 x))
asymm-to-symm-int (negint x) = nzeroint (negint (p1 x))

syasy-int : ( n : AsymmInt ) -> ( definition-equal ( symm-to-asymm-int ( asymm-to-symm-int n ) ) n ) 
syasy-int (natint zero) = 🐓🥚
syasy-int (natint (suc x)) = 🐓🥚
syasy-int (negint zero) = 🐓🥚 
syasy-int (negint (suc x)) = 🐓🥚

asysy-int : ( n : Int ) -> ( definition-equal ( asymm-to-symm-int ( symm-to-asymm-int n ) ) n ) 
asysy-int (nzeroint (posint (p1 x))) = 🐓🥚
asysy-int (nzeroint (negint (p1 x))) = 🐓🥚
asysy-int zero-int = 🐓🥚