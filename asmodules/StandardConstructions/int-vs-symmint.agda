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

data AsymmInt : Set where 
    natint : Nat -> AsymmInt
    negint : Nat -> AsymmInt

data SymmInt : Set where 
    pos : Pos -> SymmInt 
    int-zero :   SymmInt
    neg : Pos -> SymmInt 

