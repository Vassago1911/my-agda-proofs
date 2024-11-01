module StandardConstructions.Integers2 where

open import StandardConstructions.IdentityType
    using ( definition-equal; 🐓🥚; cong; sym; trans; extensionality)
open import StandardConstructions.Maps
    using ( circ ; id )
open import StandardConstructions.Naturals
    using ( Nat; zero; suc; add; mul; r-add-zero; add-comm; suc-skip-add; add-ass; r-one-neutral; mul-def-reverse; mul-comm; r-zero-absorbs; nat-suc-splitter )

data Int : Set where
    nat-int : Nat -> Int
    neg-int : Nat -> Int

nat-diff-to-int : Nat -> Nat -> Int
nat-diff-to-int zero zero = nat-int zero
nat-diff-to-int zero (suc m) = neg-int m
nat-diff-to-int (suc n) zero = nat-int (suc n)
nat-diff-to-int (suc n) (suc m) = nat-diff-to-int n m

nat-diff-to-int-zero-is-eq : ( n m : Nat ) -> ( definition-equal ( nat-diff-to-int n m ) (nat-int zero) )
                                           -> ( definition-equal n m ) 
nat-diff-to-int-zero-is-eq zero zero pred = 🐓🥚
nat-diff-to-int-zero-is-eq (suc n) (suc m) pred = ind-step
    where ind-step = cong suc ( nat-diff-to-int-zero-is-eq n m pred )                                                                        

int-suc : Int -> Int
int-suc (nat-int x) = nat-int (suc x)
int-suc (neg-int zero) = nat-int zero
int-suc (neg-int (suc x)) = neg-int x

int-pred : Int -> Int
int-pred (nat-int zero) = neg-int zero
int-pred (nat-int (suc x)) = nat-int x
int-pred (neg-int x) = neg-int (suc x)

int-predsuc-id : ( n : Int ) -> ( definition-equal ( int-pred (int-suc n ) ) n )
int-predsuc-id (nat-int zero) = 🐓🥚
int-predsuc-id (nat-int (suc x)) = 🐓🥚
int-predsuc-id (neg-int zero) = 🐓🥚
int-predsuc-id (neg-int (suc x)) = 🐓🥚

int-sucpred-id : ( n : Int ) -> ( definition-equal ( int-suc ( int-pred n ) ) n )
int-sucpred-id (nat-int zero) = 🐓🥚
int-sucpred-id (nat-int (suc x)) = 🐓🥚
int-sucpred-id (neg-int zero) = 🐓🥚
int-sucpred-id (neg-int (suc x)) = 🐓🥚

int-add : Int -> Int -> Int
int-add (nat-int x) (nat-int y) = nat-int (add x y)
int-add (nat-int x) (neg-int y) = nat-diff-to-int x (suc y)
int-add (neg-int x) (nat-int y) = nat-diff-to-int y (suc x)
int-add (neg-int x) (neg-int y) = neg-int (suc (add x y))

int-add-one-suc : ( n : Int ) -> ( definition-equal ( int-add (nat-int (suc zero)) n ) ( int-suc n ) ) 
int-add-one-suc (nat-int zero) = 🐓🥚
int-add-one-suc (nat-int (suc x)) = 🐓🥚
int-add-one-suc (neg-int zero) = 🐓🥚
int-add-one-suc (neg-int (suc x)) = 🐓🥚

int-add-comm : ( n m : Int ) -> ( definition-equal ( int-add n m ) ( int-add m n ) )
int-add-comm (nat-int x) (nat-int y)
    rewrite ( add-comm {y} {x} )     = 🐓🥚
int-add-comm (neg-int x) (neg-int y)
    rewrite ( add-comm {y} {x} )     = 🐓🥚
int-add-comm (nat-int x) (neg-int y) = 🐓🥚
int-add-comm (neg-int x) (nat-int y) = 🐓🥚

int-add-zero : ( n : Int ) -> ( definition-equal ( int-add n ( nat-int zero ) ) n )
int-add-zero (nat-int x)
    rewrite ( r-add-zero {x} ) = 🐓🥚
int-add-zero (neg-int x)       = 🐓🥚

nat-diff-nat-add : ( a b r : Nat )
                ->
                ( definition-equal
                    ( int-add ( nat-diff-to-int a b ) ( nat-int r ) )
                    ( nat-diff-to-int ( add a r ) b ) )
nat-diff-nat-add zero zero zero = 🐓🥚
nat-diff-nat-add (suc a) zero zero = 🐓🥚
nat-diff-nat-add zero zero (suc r) = 🐓🥚
nat-diff-nat-add (suc a) zero (suc r) = 🐓🥚
nat-diff-nat-add zero (suc b) r = 🐓🥚
nat-diff-nat-add (suc a) (suc b) zero
    rewrite ( int-add-zero ( nat-diff-to-int a b ) )
    rewrite ( r-add-zero {a})
    = 🐓🥚
nat-diff-nat-add (suc a) (suc b) (suc r)
    rewrite (nat-diff-nat-add a b (suc r ) )
    = 🐓🥚

nat-diff-neg-add : ( a b r : Nat )
                ->
                ( definition-equal
                    ( int-add ( nat-diff-to-int a b ) ( neg-int r ) )
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
                ( int-add ( nat-int a ) ( nat-diff-to-int b c ) )
                ( nat-diff-to-int ( add a b ) c ) )
add-nat-diff a b c
    rewrite ( int-add-comm ( nat-int a ) ( nat-diff-to-int b c ) )
    rewrite ( nat-diff-nat-add b c a )
    rewrite ( add-comm {b} {a} )
    = 🐓🥚

add-neg-diff : ( a b c : Nat )
        -> ( definition-equal
                ( int-add ( neg-int a ) ( nat-diff-to-int b c ) )
                ( nat-diff-to-int b ( suc ( add a c ) ) ) )
add-neg-diff a b c
    rewrite ( int-add-comm ( neg-int a ) ( nat-diff-to-int b c ) )
    rewrite ( nat-diff-neg-add b c a )
    rewrite ( add-comm {c} {a} )
    = 🐓🥚

int-add-ass : ( k l m : Int )
        -> ( definition-equal
                ( int-add ( int-add k l ) m )
                ( int-add k ( int-add l m ) ) )
int-add-ass (nat-int zero) l m
   rewrite ( int-add-comm (nat-int zero) l )
   rewrite ( int-add-comm (nat-int zero) (int-add l m ) )
   rewrite ( int-add-zero (int-add l m) )
   rewrite ( int-add-zero l )
   = 🐓🥚
int-add-ass k (nat-int zero) m
   rewrite ( int-add-comm (nat-int zero) k )
   rewrite ( int-add-comm (nat-int zero) m )
   rewrite ( int-add-zero k )
   rewrite ( int-add-zero m )
   = 🐓🥚
int-add-ass k l (nat-int zero)
    rewrite ( int-add-zero ( int-add k l ) )
    rewrite ( int-add-zero l )
    = 🐓🥚

int-add-ass (neg-int x)       (neg-int y)       (nat-int (suc z))
    rewrite ( int-add-comm ( neg-int x ) ( nat-diff-to-int z y ) )
    rewrite ( nat-diff-neg-add z y x )
    rewrite ( add-comm {y} {x} )
    = 🐓🥚

int-add-ass (neg-int x)       (nat-int (suc y)) (nat-int (suc z))
    rewrite ( nat-diff-nat-add y x (suc z) )
    = 🐓🥚

int-add-ass (nat-int (suc x)) (neg-int y)       (neg-int z)
    rewrite ( nat-diff-neg-add x y z )
    = 🐓🥚

int-add-ass (nat-int (suc x)) (neg-int y)       (nat-int (suc z))
    rewrite ( nat-diff-nat-add x y (suc z) )
    rewrite ( int-add-comm (nat-int (suc x)) ( nat-diff-to-int z y ) )
    rewrite ( nat-diff-nat-add z y ( suc x ) )
    rewrite ( suc-skip-add {x} {z} )
    rewrite ( suc-skip-add {z} {x} )
    rewrite ( add-comm {z} {x} )
    = 🐓🥚

int-add-ass (nat-int (suc x)) (nat-int (suc y)) (neg-int z)
    rewrite ( int-add-comm ( nat-int ( suc x ) ) ( nat-diff-to-int y z ) )
    rewrite ( nat-diff-nat-add y z (suc x) )
    rewrite ( suc-skip-add {x} {y} )
    rewrite ( suc-skip-add {y} {x} )
    rewrite ( add-comm {y} {x} )
    = 🐓🥚

int-add-ass (neg-int x)       (neg-int y)       (neg-int z)
    rewrite ( suc-skip-add {x} {add y z} )
    rewrite ( add-ass {x} {y} {z} )
    = 🐓🥚

int-add-ass (neg-int x)       (nat-int (suc y)) (neg-int z)
    rewrite ( int-add-comm (neg-int x) ( nat-diff-to-int y z ) )
    rewrite ( nat-diff-neg-add y x z )
    rewrite ( nat-diff-neg-add y z x )
    rewrite ( add-comm {z} {x} )
    = 🐓🥚

int-add-ass (nat-int (suc x)) (nat-int (suc y)) (nat-int (suc z))
    rewrite ( suc-skip-add {x} {y} )
    rewrite ( suc-skip-add {x} {add y (suc z)} )
    rewrite ( add-ass {x} {y} {suc z} )
    = 🐓🥚

add-has-inverses : ( a : Nat ) -> ( definition-equal ( int-add ( nat-int (suc a) ) ( neg-int a ) ) (nat-int zero) )
add-has-inverses zero = 🐓🥚
add-has-inverses (suc a)
    rewrite ( add-has-inverses a )
    = 🐓🥚

add-nat-inverse-unique : ( a : Nat ) -> ( p : Int ) 
            -> ( definition-equal ( int-add (nat-int (suc a)) p ) (nat-int zero) ) 
            -> ( definition-equal p (neg-int a) ) 
add-nat-inverse-unique zero p pred 
    rewrite ( int-add-one-suc p )     
    = res
    where step = cong int-pred pred
          iso-inv = sym ( int-predsuc-id p ) 
          res = trans iso-inv step           
add-nat-inverse-unique (suc a) (neg-int (suc x)) pred     
    = cong neg-int (cong suc step)
    where step = sym ( nat-diff-to-int-zero-is-eq a x pred )    

add-neg-inverse-unique : ( a : Nat ) -> ( p : Int ) 
                -> ( definition-equal ( int-add (neg-int a) p ) (nat-int zero) ) 
                -> ( definition-equal p ( nat-int (suc a) ) ) 
add-neg-inverse-unique zero (nat-int (suc x)) pred     
    = step-pred
    where step-pred = cong nat-int ( cong suc ( nat-diff-to-int-zero-is-eq x zero pred ) )
add-neg-inverse-unique (suc a) (nat-int x) pred 
    = step-pred                
    where step-pred = cong nat-int ( nat-diff-to-int-zero-is-eq x (suc (suc a) ) pred )

add-zero-inverse-unique : ( p : Int )
                -> ( definition-equal ( int-add (nat-int zero) p ) ( nat-int zero) ) 
                -> ( definition-equal p (nat-int zero ) ) 
add-zero-inverse-unique (nat-int zero) pred = 🐓🥚                

int-add-inverse : Int -> Int 
int-add-inverse (nat-int zero) = nat-int zero
int-add-inverse (nat-int (suc x)) = neg-int x
int-add-inverse (neg-int x) = nat-int (suc x)

add-inverse-unique : ( p q : Int ) 
            -> ( definition-equal ( int-add p q ) ( nat-int zero ) ) 
            -> ( definition-equal q ( int-add-inverse p ) ) 
add-inverse-unique (nat-int zero) q = add-zero-inverse-unique q
add-inverse-unique (nat-int (suc x)) q = add-nat-inverse-unique x q
add-inverse-unique (neg-int x) q = add-neg-inverse-unique x q            

int-add-reduction : ( a b : Nat ) -> ( definition-equal ( int-add ( nat-int (suc a) ) ( neg-int (suc b ) ) )
                                                        ( int-add ( nat-int a ) ( neg-int b ) ) )
int-add-reduction a b = 🐓🥚

int-mul : Int -> Int -> Int
int-mul a b = {!   !}