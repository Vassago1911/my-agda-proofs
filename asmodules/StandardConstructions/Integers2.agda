module StandardConstructions.Integers2 where

open import StandardConstructions.IdentityType
    using ( definition-equal; 🐓🥚; cong; sym; trans; extensionality)
open import StandardConstructions.Maps
    using ( circ ; id )
open import StandardConstructions.Naturals
    using ( Nat; zero; suc; add; mul; r-add-zero; add-comm; suc-skip-add; add-ass; r-one-neutral; 
            mul-def-reverse; mul-def-reverse1; mul-comm; r-zero-absorbs; nat-suc-splitter; mul-ass;
            ldist-mul; rdist-mul )

data Int : Set where
    nat-int : Nat -> Int
    neg-int : Nat -> Int

nat-diff-to-int : Nat -> Nat -> Int
nat-diff-to-int zero zero = nat-int zero
nat-diff-to-int zero (suc m) = neg-int m
nat-diff-to-int (suc n) zero = nat-int (suc n)
nat-diff-to-int (suc n) (suc m) = nat-diff-to-int n m

nat-diff-eq-is-zero : ( n : Nat ) -> ( definition-equal ( nat-diff-to-int n n ) (nat-int zero) ) 
nat-diff-eq-is-zero zero = 🐓🥚
nat-diff-eq-is-zero (suc n) = nat-diff-eq-is-zero n

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

int-add-inverse-is-inverse : ( n : Int ) -> ( definition-equal ( int-add n ( int-add-inverse n ) ) (nat-int zero) ) 
int-add-inverse-is-inverse (nat-int zero) = 🐓🥚
int-add-inverse-is-inverse (nat-int (suc x)) = nat-diff-eq-is-zero x
int-add-inverse-is-inverse (neg-int x) = nat-diff-eq-is-zero x

add-inverse-unique : ( p q : Int ) 
            -> ( definition-equal ( int-add p q ) ( nat-int zero ) ) 
            -> ( definition-equal q ( int-add-inverse p ) ) 
add-inverse-unique (nat-int zero) q = add-zero-inverse-unique q
add-inverse-unique (nat-int (suc x)) q = add-nat-inverse-unique x q
add-inverse-unique (neg-int x) q = add-neg-inverse-unique x q            

int-add-inverse-additive : ( n m : Int ) -> ( definition-equal 
                                                               ( int-add ( int-add-inverse n ) ( int-add-inverse m ) ) 
                                                               ( int-add-inverse ( int-add n m ) ) 
                                                               ) 
int-add-inverse-additive n m = step
    where addnm-to-tentative-is-zero : ( n m : Int ) ->  
            ( definition-equal 
                    ( int-add ( int-add n m ) ( int-add (int-add-inverse n) (int-add-inverse m) )  )  
                    ( nat-int zero ) ) 
          addnm-to-tentative-is-zero n m 
            rewrite ( int-add-ass n m (int-add (int-add-inverse n) (int-add-inverse m)) ) 
            rewrite ( int-add-comm (int-add-inverse n) (int-add-inverse m) ) 
            rewrite ( sym ( int-add-ass m (int-add-inverse m) (int-add-inverse n) ) )
            rewrite ( int-add-inverse-is-inverse m ) 
            rewrite ( sym ( int-add-ass n (nat-int zero) (int-add-inverse n) ) )
            rewrite ( int-add-comm n (nat-int zero) ) 
            rewrite ( int-add-ass (nat-int zero) n (int-add-inverse n))             
            rewrite ( int-add-inverse-is-inverse n ) 
            rewrite ( int-add-zero (nat-int zero) ) 
            = 🐓🥚 
          step = add-inverse-unique (( int-add n m )) (( int-add (int-add-inverse n) (int-add-inverse m) )) ( addnm-to-tentative-is-zero n m ) 

int-add-inverse-square-id : ( n : Int ) -> ( definition-equal ( int-add-inverse ( int-add-inverse n ) ) n ) 
int-add-inverse-square-id (nat-int zero) = 🐓🥚
int-add-inverse-square-id (nat-int (suc x)) = 🐓🥚
int-add-inverse-square-id (neg-int x) = 🐓🥚

int-add-reduction : ( a b : Nat ) -> ( definition-equal ( int-add ( nat-int (suc a) ) ( neg-int (suc b ) ) )
                                                        ( int-add ( nat-int a ) ( neg-int b ) ) )
int-add-reduction a b = 🐓🥚

int-mul : Int -> Int -> Int
int-mul (nat-int x) (nat-int y) = nat-int ( mul x y )
int-mul (nat-int x) (neg-int y) = int-add-inverse ( nat-int ( mul x (suc y) ) )
int-mul (neg-int x) (nat-int y) = int-add-inverse ( nat-int ( mul (suc x) y ) )  
int-mul (neg-int x) (neg-int y) = int-add-inverse ( int-add-inverse ( nat-int ( mul (suc x) (suc y) ) ) )

int-mul-comm : ( n m : Int ) -> ( definition-equal ( int-mul n m ) ( int-mul m n ) ) 
int-mul-comm (nat-int x) (nat-int y) 
    rewrite ( mul-comm {y} {x} ) 
    = 🐓🥚
int-mul-comm (nat-int x) (neg-int y) 
    rewrite ( mul-def-reverse1 x y )
    rewrite ( mul-comm {y} {x} ) 
    = 🐓🥚
int-mul-comm (neg-int x) (nat-int y) 
    rewrite ( mul-def-reverse1 y x ) 
    rewrite ( mul-comm {y} {x} ) 
    = 🐓🥚
int-mul-comm (neg-int x) (neg-int y) 
    rewrite ( mul-def-reverse1 x y ) 
    rewrite ( mul-def-reverse1 y x ) 
    rewrite ( mul-comm {y} {x} ) 
    rewrite ( sym ( add-ass {y} {x} {mul x y} ) ) 
    rewrite ( sym ( add-ass {x} {y} {mul x y} ) ) 
    rewrite ( add-comm {y} {x} ) 
    = 🐓🥚

int-mul-pull-inv-from-left : ( p q : Int ) -> ( definition-equal ( int-mul ( int-add-inverse p ) q ) ( int-add-inverse ( int-mul p q ) ) ) 
int-mul-pull-inv-from-left (nat-int zero) (nat-int y) = 🐓🥚
int-mul-pull-inv-from-left (nat-int (suc x)) (nat-int y) = 🐓🥚
int-mul-pull-inv-from-left (nat-int zero) (neg-int y) = 🐓🥚
int-mul-pull-inv-from-left (nat-int (suc x)) (neg-int y) = 🐓🥚
int-mul-pull-inv-from-left (neg-int zero) (nat-int zero) = 🐓🥚
int-mul-pull-inv-from-left (neg-int x) (nat-int (suc y)) = 🐓🥚
int-mul-pull-inv-from-left (neg-int x) (neg-int y) = 🐓🥚
int-mul-pull-inv-from-left (neg-int (suc x)) (nat-int zero) 
    rewrite ( r-zero-absorbs {x} ) 
    rewrite ( int-add-inverse-square-id (nat-int x) ) 
    = 🐓🥚

int-mul-pull-inv-from-right : ( p q : Int ) -> ( definition-equal ( int-mul p ( int-add-inverse q ) ) ( int-add-inverse ( int-mul p q ) ) ) 
int-mul-pull-inv-from-right p q 
    rewrite ( int-mul-comm p (int-add-inverse q) ) 
    rewrite ( int-mul-pull-inv-from-left q p ) 
    rewrite ( int-mul-comm q p ) 
    = 🐓🥚 

int-mul-ass : ( p q r : Int ) -> ( definition-equal ( int-mul ( int-mul p q ) r ) ( int-mul p ( int-mul q r ) ) ) 
int-mul-ass (nat-int x) (nat-int y) (nat-int z) = cong nat-int (mul-ass {x} {y} {z})
int-mul-ass (nat-int x) (nat-int y) (neg-int z) 
    rewrite ( int-mul-pull-inv-from-right (nat-int x) (nat-int (mul y (suc z))) )
    rewrite ( mul-ass {x} {y} {suc z} ) 
    = 🐓🥚
int-mul-ass (nat-int x) (neg-int y) (nat-int z) 
    rewrite ( int-mul-pull-inv-from-right (nat-int x) (nat-int (add z (mul y z))) )
    rewrite ( int-mul-pull-inv-from-left (nat-int (mul x (suc y))) (nat-int z) )
    rewrite ( mul-ass {x} {suc y} {z} )     
    = 🐓🥚
int-mul-ass (nat-int x) (neg-int y) (neg-int z) 
    rewrite ( int-mul-pull-inv-from-left  (nat-int (mul x (suc y))) (neg-int z) )
    rewrite ( int-add-inverse-square-id (nat-int (mul (mul x (suc y)) (suc z))) )
    rewrite ( mul-ass {x} {suc y} {suc z} ) 
    = 🐓🥚
int-mul-ass (neg-int x) (nat-int y) (nat-int z) 
    rewrite ( int-mul-pull-inv-from-left (nat-int (add y (mul x y))) (nat-int z) )
    rewrite ( sym ( mul-ass {x} {y} {z} ) )
    rewrite ( sym ( rdist-mul {y} {mul x y} {z} ) )      
    = 🐓🥚
int-mul-ass (neg-int x) (nat-int y) (neg-int z) 
    rewrite ( int-mul-pull-inv-from-left (nat-int (add y (mul x y))) (neg-int z))
    rewrite ( int-mul-pull-inv-from-right (neg-int x) (nat-int (mul y (suc z))) )
    rewrite ( sym ( mul-ass {x} {y} {suc z} ) ) 
    rewrite ( rdist-mul { y } {mul x y} {suc z} )     
    = 🐓🥚
int-mul-ass (neg-int x) (neg-int y) (nat-int z) 
    rewrite ( int-mul-pull-inv-from-right (neg-int x) (nat-int (add z (mul y z))) ) 
    rewrite ( int-add-inverse-square-id (nat-int (add (add z (mul y z)) (mul x (add z (mul y z)))) ) )         
    rewrite ( add-ass {z} {mul y z} {mul x (add z (mul y z))} ) 
    rewrite ( sym ( rdist-mul {y} {mul x (suc y)} {z} ) ) 
    rewrite (mul-ass {x} {suc y} {z} ) 
    = 🐓🥚 
int-mul-ass (neg-int x) (neg-int y) (neg-int z) 
    rewrite ( add-ass {z} {(mul y (suc z))} {(mul x (suc (add z (mul y (suc z))))) } ) 
    rewrite ( sym ( rdist-mul {y} {mul x (suc y)} {suc z} ) ) 
    rewrite (mul-ass {x} {suc y} {suc z} ) 
    = 🐓🥚

int-mul-zero-absorbs : ( p : Int ) -> ( definition-equal ( int-mul ( nat-int zero) p ) ( nat-int zero) ) 
int-mul-zero-absorbs (nat-int x) = 🐓🥚
int-mul-zero-absorbs (neg-int x) = 🐓🥚

int-mul-one-neutral : ( p : Int ) -> ( definition-equal ( int-mul ( nat-int (suc zero) ) p ) p ) 
int-mul-one-neutral (nat-int x) 
    rewrite ( r-add-zero {x} ) = 🐓🥚
int-mul-one-neutral (neg-int x) 
    rewrite ( r-add-zero {x} ) = 🐓🥚

int-mul-suc-step : ( l : Nat ) -> ( p : Int ) 
        -> ( definition-equal 
                ( int-add p ( int-mul ( nat-int l ) p ) )
                ( int-mul ( nat-int (suc l)) p ) ) 
int-mul-suc-step zero p 
    rewrite ( int-mul-zero-absorbs p ) 
    rewrite ( int-mul-one-neutral p ) 
    rewrite ( int-add-zero p ) 
    = 🐓🥚
int-mul-suc-step (suc l) (nat-int zero) = 🐓🥚
int-mul-suc-step (suc l) (nat-int (suc x)) = 🐓🥚
int-mul-suc-step (suc l) (neg-int x) 
    rewrite ( suc-skip-add {x} {(add x (mul l (suc x)))} ) 
    = 🐓🥚

int-mul-neg-step : ( l : Nat ) -> ( p : Int ) 
        -> ( definition-equal 
                ( int-add ( int-add-inverse p ) ( int-mul ( neg-int l ) p ) ) 
                ( int-mul ( neg-int (suc l) ) p ) )  
int-mul-neg-step zero (nat-int x) 
    rewrite ( int-add-inverse-additive (nat-int x) ( nat-int (add x zero ) ) ) 
    = 🐓🥚
int-mul-neg-step zero (neg-int x) = 🐓🥚
int-mul-neg-step (suc l) (nat-int x) 
    rewrite ( int-add-inverse-additive (nat-int x) ( nat-int (add x (add x (mul l x) ) ) ) ) 
    = 🐓🥚
int-mul-neg-step (suc l) (neg-int x) = 🐓🥚

int-mul-ldist-nat : ( l : Nat ) -> ( p q : Int ) -> ( definition-equal 
                                                      ( int-add ( int-mul ( nat-int l ) p ) ( int-mul ( nat-int l ) q ) ) 
                                                      ( int-mul ( nat-int l ) ( int-add p q ) )) 
int-mul-ldist-nat zero p q 
    rewrite ( int-mul-zero-absorbs p ) 
    rewrite ( int-mul-zero-absorbs q ) 
    rewrite ( int-mul-zero-absorbs (int-add p q) ) 
    = 🐓🥚  
int-mul-ldist-nat (suc l) p q 
    rewrite ( sym ( int-mul-suc-step l p ) )
    rewrite ( sym ( int-mul-suc-step l q ) )
    rewrite ( sym ( int-mul-suc-step l (int-add p q) ) )
    rewrite ( int-add-ass p (int-mul (nat-int l) p) (int-add q (int-mul (nat-int l) q)) ) 
    rewrite ( sym ( int-add-ass (int-mul (nat-int l) p) q (int-mul (nat-int l) q) ) ) 
    rewrite ( int-add-comm (int-mul (nat-int l) p) q ) 
    rewrite ( int-add-ass q (int-mul (nat-int l) p) (int-mul (nat-int l) q) ) 
    rewrite ( sym ( int-add-ass p q (int-add (int-mul (nat-int l) p) (int-mul (nat-int l) q))) ) 
    rewrite ( int-mul-ldist-nat l p q ) 
    = 🐓🥚

int-mul-neg-int-zero : ( p : Int ) -> ( definition-equal 
                                            ( int-mul (neg-int zero) p ) 
                                            ( int-add-inverse p ) ) 
int-mul-neg-int-zero (nat-int zero) = 🐓🥚
int-mul-neg-int-zero (nat-int (suc x)) 
    rewrite (r-add-zero {x} ) 
    = 🐓🥚
int-mul-neg-int-zero (neg-int x) 
    rewrite (r-add-zero {x} ) 
    = 🐓🥚                                            

int-mul-ldist-neg : ( l : Nat ) -> ( p q : Int ) -> ( definition-equal  
                                                      ( int-add ( int-mul ( neg-int l ) p ) ( int-mul ( neg-int l ) q ) ) 
                                                      ( int-mul ( neg-int l ) ( int-add p q ) )) 
int-mul-ldist-neg zero p q 
    rewrite ( int-mul-neg-int-zero p ) 
    rewrite ( int-mul-neg-int-zero q ) 
    rewrite ( int-mul-neg-int-zero (int-add p q ) ) 
    rewrite ( int-add-inverse-additive p q ) 
    = 🐓🥚   
int-mul-ldist-neg (suc l) p q 
    rewrite ( sym ( int-mul-neg-step l p ) ) 
    rewrite ( sym ( int-mul-neg-step l q ) ) 
    rewrite ( sym ( int-mul-neg-step l (int-add p q ) ) ) 
    rewrite ( int-add-ass (int-add-inverse p) (int-mul (neg-int l) p) (int-add (int-add-inverse q) (int-mul (neg-int l) q)) )
    rewrite ( sym ( int-add-ass (int-mul (neg-int l) p) (int-add-inverse q) (int-mul (neg-int l) q) ) ) 
    rewrite ( int-add-comm  (int-mul (neg-int l) p) (int-add-inverse q) ) 
    rewrite ( int-add-ass (int-add-inverse q) (int-mul (neg-int l) p) (int-mul (neg-int l) q) )  
    rewrite ( sym ( int-add-ass (int-add-inverse p) (int-add-inverse q) (int-add (int-mul (neg-int l) p) (int-mul (neg-int l) q)) )  )
    rewrite ( int-add-inverse-additive p q ) 
    rewrite ( int-mul-ldist-neg l p q ) 
    = 🐓🥚

int-mul-ldist : ( l : Int ) -> ( p q : Int ) -> ( definition-equal 
                                                    ( int-add ( int-mul l p ) ( int-mul l q ) ) 
                                                    ( int-mul l ( int-add p q ) ) ) 
int-mul-ldist (nat-int x) p q = int-mul-ldist-nat x p q 
int-mul-ldist (neg-int x) p q = int-mul-ldist-neg x p q

int-mul-rdist : ( r : Int ) -> ( p q : Int ) -> ( definition-equal 
                                                    ( int-add ( int-mul p r ) ( int-mul q r ) ) 
                                                    ( int-mul ( int-add p q ) r ) ) 
int-mul-rdist r p q 
    rewrite ( int-mul-comm p r ) 
    rewrite ( int-mul-comm q r ) 
    rewrite ( int-mul-comm (int-add p q) r ) 
    rewrite ( int-mul-ldist r p q ) 
    = 🐓🥚                                                    