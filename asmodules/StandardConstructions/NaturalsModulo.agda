module StandardConstructions.NaturalsModulo where 

open import StandardConstructions.Boolean using ( Boolean; true; false ) 
open import StandardConstructions.IdentityType using ( definition-equal; 🐓🥚; cong; sym) 
open import StandardConstructions.Naturals using ( Nat; zero; suc; add; mul; r-add-zero ) 

div-helper : (k m n j : Nat) → Nat
div-helper k m  zero    j      = k
div-helper k m (suc n)  zero   = div-helper (suc k) m n m
div-helper k m (suc n) (suc j) = div-helper k       m n j

mod-helper : (k m n j : Nat) → Nat
mod-helper k m  zero    j      = k
mod-helper k m (suc n)  zero   = mod-helper zero        m n m
mod-helper k m (suc n) (suc j) = mod-helper (suc k) m n j

{-# BUILTIN NATDIVSUCAUX div-helper #-}
{-# BUILTIN NATMODSUCAUX mod-helper #-}

modBy : Nat -> Nat -> Nat 
modBy n zero = zero 
modBy n (suc m) = mod-helper zero m n m

divBy : Nat -> Nat -> Nat 
divBy n zero = zero 
divBy n ( suc m ) = div-helper zero m n m 
