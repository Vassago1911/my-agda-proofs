module StandardConstructions.Integers2 where

open import StandardConstructions.IdentityType
    using ( definition-equal; 🐓🥚; cong; sym; extensionality)
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

int-add-reduction : ( a b : Nat ) -> ( definition-equal ( int-add ( nat-int (suc a) ) ( neg-int (suc b ) ) )
                                                        ( int-add ( nat-int a ) ( neg-int b ) ) )
int-add-reduction a b = 🐓🥚

int-mul : Int -> Int -> Int
int-mul (nat-int zero) z = nat-int zero
int-mul z (nat-int zero) = nat-int zero

int-mul (nat-int (suc x)) (neg-int zero) = neg-int x
int-mul (neg-int zero) (nat-int (suc y)) = neg-int y

int-mul (nat-int (suc x)) (nat-int (suc y)) = nat-int (mul (suc x) (suc y) )
int-mul (neg-int x) (neg-int y) = nat-int (mul (suc x) (suc y) )
int-mul (nat-int (suc x)) (neg-int (suc y)) = int-suc ( neg-int ( mul (suc x) ( suc (suc y ) ) ) )
int-mul (neg-int (suc x)) (nat-int (suc y)) = int-suc ( neg-int ( mul (suc (suc x) ) (suc y) ) )

int-mul-zero : ( p : Int ) -> ( definition-equal ( int-mul p (nat-int zero) ) (nat-int zero) )
int-mul-zero (nat-int zero) = 🐓🥚
int-mul-zero (nat-int (suc x)) = 🐓🥚
int-mul-zero (neg-int x) = 🐓🥚

int-mul-one : ( p : Int ) -> ( definition-equal ( int-mul p (nat-int (suc zero) ) ) p )
int-mul-one (nat-int zero) = 🐓🥚
int-mul-one (nat-int (suc x))
   rewrite ( r-one-neutral {x} )
   = 🐓🥚
int-mul-one (neg-int zero) = 🐓🥚
int-mul-one (neg-int (suc x))
    rewrite (r-one-neutral {x} )
    = 🐓🥚

int-mul-pos : ( n : Nat ) -> ( definition-equal ( int-mul (neg-int zero) (nat-int (suc n) ) ) ( neg-int n ) )
int-mul-pos n = 🐓🥚

int-mul-neg : ( n : Nat ) -> ( definition-equal ( int-mul (neg-int zero) (neg-int n ) ) ( nat-int (suc n) ) )
int-mul-neg zero = 🐓🥚
int-mul-neg (suc n)
    rewrite (r-add-zero {n} )
    = 🐓🥚

int-mul-negneg : ( n m : Nat ) -> ( definition-equal ( int-mul (neg-int n) (neg-int m) ) ( int-mul ( nat-int (suc n ) ) ( nat-int (suc m ) ) ) )
int-mul-negneg n m = 🐓🥚

int-mul-neg-nat-comm : (n m : Nat ) -> ( definition-equal ( int-mul (nat-int n) (neg-int m ) ) ( int-mul (neg-int m) ( nat-int n ) ) )
int-mul-neg-nat-comm zero m = 🐓🥚
int-mul-neg-nat-comm (suc n) zero = 🐓🥚
int-mul-neg-nat-comm (suc n) (suc m)
    rewrite ( suc-skip-add {n} {add n (mul m (suc n))} )
    rewrite ( mul-comm {n} {suc (suc m) } )
    rewrite ( mul-comm {m} {suc n} )
    rewrite ( mul-comm {n} {m} )
    rewrite ( sym ( add-ass {m} {n} {add n (mul m n)} ) )
    rewrite ( add-comm {m} {n} )
    rewrite ( add-ass {n} {m} {add n (mul m n) } )
    rewrite ( sym ( add-ass {m} {n} {mul m n} ) )
    rewrite ( add-comm {m} {n} )
    rewrite ( add-ass {n} {m} {mul m n} )
    = 🐓🥚

int-mul-comm : ( p q : Int ) -> ( definition-equal ( int-mul p q ) ( int-mul q p ) )
int-mul-comm (nat-int zero) (nat-int zero) = 🐓🥚
int-mul-comm (nat-int zero) (neg-int y) = 🐓🥚
int-mul-comm (nat-int (suc x)) (nat-int zero) = 🐓🥚
int-mul-comm (neg-int x) (nat-int zero) = 🐓🥚
int-mul-comm (nat-int zero) (nat-int (suc y)) = 🐓🥚
int-mul-comm (nat-int (suc x)) (neg-int zero) = 🐓🥚
int-mul-comm (neg-int zero) (nat-int (suc y)) = 🐓🥚
int-mul-comm (nat-int (suc x)) (nat-int (suc y))
    rewrite ( mul-comm {suc x} {suc y} )
    = 🐓🥚
int-mul-comm (neg-int x) (neg-int y)
    rewrite ( mul-comm {suc x} {suc y} )
    = 🐓🥚
int-mul-comm (nat-int (suc x)) (neg-int (suc y))
    rewrite ( int-mul-neg-nat-comm (suc x) ( suc y) )
    = 🐓🥚
int-mul-comm (neg-int (suc x)) (nat-int (suc y))
    rewrite ( sym ( int-mul-neg-nat-comm (suc y) ( suc x) ) )
    = 🐓🥚

nat-int-mul-hom : ( n m : Nat ) -> ( definition-equal ( int-mul ( nat-int n ) ( nat-int m ) )
                                                      ( nat-int (mul n m ) ) )
nat-int-mul-hom zero m = 🐓🥚
nat-int-mul-hom (suc n) zero
    rewrite ( r-zero-absorbs {suc n} )
   = 🐓🥚
nat-int-mul-hom (suc n) (suc m) = 🐓🥚

int-mul-negpos : ( n m : Nat ) -> ( definition-equal ( int-mul ( neg-int n ) ( nat-int (suc m ) ) )
                                                     ( int-mul ( nat-int (suc n) ) ( neg-int m ) ) )
int-mul-negpos zero zero = 🐓🥚
int-mul-negpos zero (suc m)
    rewrite (int-mul-pos (suc m) )
    rewrite (r-add-zero {m} )
    = 🐓🥚
int-mul-negpos (suc n) zero
    rewrite ( r-one-neutral {n} )
    = 🐓🥚
int-mul-negpos (suc n) (suc m) = 🐓🥚

int-mul-minus-one : ( n : Nat ) -> ( definition-equal ( int-mul ( neg-int zero ) ( nat-int (suc n) ) )
                                                      ( neg-int n ) )
int-mul-minus-one zero = 🐓🥚
int-mul-minus-one (suc n) = 🐓🥚

int-mul-minus-one-t : ( n : Nat ) -> ( definition-equal ( int-mul (neg-int zero) ( neg-int n ) )
                                                        ( nat-int (suc n) ) )
int-mul-minus-one-t zero = 🐓🥚
int-mul-minus-one-t (suc n)
    rewrite ( r-add-zero {n} )
    = 🐓🥚

int-mul-minus-one-zero : ( definition-equal ( int-mul (neg-int zero) (nat-int zero) )
                                            ( nat-int zero ) )
int-mul-minus-one-zero = 🐓🥚

int-mul-minus-one-minus-one : (definition-equal (int-mul (neg-int zero) ( neg-int zero) ) ( nat-int (suc zero ) ) )
int-mul-minus-one-minus-one = 🐓🥚

int-mul-suc-nat : ( n m : Nat ) -> ( definition-equal ( int-mul (nat-int (suc n) ) ( nat-int m) )
                                                  ( int-add (nat-int m) ( int-mul (nat-int n) ( nat-int m) ) ) )
int-mul-suc-nat zero zero = 🐓🥚
int-mul-suc-nat zero (suc m) = 🐓🥚
int-mul-suc-nat (suc n) zero = 🐓🥚
int-mul-suc-nat (suc n) (suc m) = 🐓🥚

int-mul-suc-neg : ( n m : Nat ) -> ( definition-equal ( int-mul (nat-int (suc n) ) ( neg-int m ) )
                                                      ( int-add (neg-int m) ( int-mul (nat-int n) (neg-int m) ) ) )
int-mul-suc-neg zero zero = 🐓🥚
int-mul-suc-neg (suc n) zero = 🐓🥚
int-mul-suc-neg zero (suc m)
    rewrite ( r-add-zero {m} )
    = 🐓🥚
int-mul-suc-neg (suc n) (suc m)
    rewrite ( suc-skip-add {m} {suc (add m (mul n (suc (suc m))))} )
    = 🐓🥚

int-mul-suc-zero : ( n m : Nat ) -> ( definition-equal ( int-mul (nat-int (suc n) ) ( nat-int zero ) )
                                                       ( int-add (nat-int zero) ( int-mul (nat-int n ) ( nat-int zero ) ) ) )
int-mul-suc-zero zero zero = 🐓🥚
int-mul-suc-zero zero (suc m) = 🐓🥚
int-mul-suc-zero (suc n) zero = 🐓🥚
int-mul-suc-zero (suc n) (suc m) = 🐓🥚

int-mul-suc : ( n : Nat ) -> ( p : Int ) -> ( definition-equal ( int-mul (nat-int (suc n) ) p )
                                                               ( int-add p ( int-mul (nat-int n) p ) ) )
int-mul-suc n (nat-int x) = int-mul-suc-nat n x
int-mul-suc n (neg-int x) = int-mul-suc-neg n x

int-mul-nat-ldist : ( n : Nat ) -> ( p q : Int ) -> ( definition-equal ( int-add (int-mul (nat-int n) p) (int-mul (nat-int n) q ) )
                                                                       ( int-mul (nat-int n) (int-add p q ) ) )
int-mul-nat-ldist zero p q = 🐓🥚
int-mul-nat-ldist (suc n) p q
    rewrite ( int-mul-suc n p )
    rewrite ( int-mul-suc n q )
    rewrite ( int-mul-suc n (int-add p q)  )
    rewrite ( int-add-ass p (int-mul (nat-int n) p) (int-add q (int-mul (nat-int n) q) ) )
    rewrite ( sym ( int-add-ass (int-mul (nat-int n) p) q (int-mul (nat-int n) q) ) )
    rewrite ( int-add-comm (int-mul (nat-int n) p) q )
    rewrite ( int-add-ass q (int-mul (nat-int n) p) (int-mul (nat-int n) q) )
    rewrite ( sym ( int-add-ass p q (int-add (int-mul (nat-int n) p) (int-mul (nat-int n) q)) ) )
    rewrite ( int-mul-nat-ldist n p q )
    = 🐓🥚

int-mul-nat-rdist : ( n : Nat ) -> ( p q : Int ) -> ( definition-equal ( int-add ( int-mul p (nat-int n) ) ( int-mul q (nat-int n) ) ) 
                                                                       ( int-mul (int-add p q) (nat-int n) ) ) 
int-mul-nat-rdist n p q 
    rewrite ( int-mul-comm p (nat-int n) )
    rewrite ( int-mul-comm q (nat-int n) ) 
    rewrite ( int-mul-comm (int-add p q ) ( nat-int n) ) 
    rewrite ( int-mul-nat-ldist n p q ) 
    = 🐓🥚

swap-nat-diff-to-int : ( n m : Nat ) -> ( definition-equal ( nat-diff-to-int n m ) ( int-mul (neg-int zero) (nat-diff-to-int m n ) ) ) 
swap-nat-diff-to-int zero zero = 🐓🥚
swap-nat-diff-to-int zero (suc m) = 🐓🥚
swap-nat-diff-to-int (suc n) zero 
    rewrite ( r-add-zero {n} ) 
    = 🐓🥚
swap-nat-diff-to-int (suc n) (suc m) = swap-nat-diff-to-int n m

int-mul-neg-suc : ( n : Nat ) -> ( p : Int ) 
            -> ( definition-equal ( int-mul (neg-int (suc n) ) p ) 
                                  ( int-add ( int-mul (neg-int zero) p ) ( int-mul ( neg-int n ) p ) ) ) 
int-mul-neg-suc n (nat-int zero) = 🐓🥚
int-mul-neg-suc n (neg-int zero) = 🐓🥚 
int-mul-neg-suc zero (nat-int (suc x)) 
    rewrite ( r-add-zero {x} ) 
    rewrite ( suc-skip-add {x} {x} ) 
    = 🐓🥚
int-mul-neg-suc (suc n) (nat-int (suc x)) 
    rewrite (suc-skip-add {x} {add x (suc (add x (mul n (suc x))))} )
    = 🐓🥚   
int-mul-neg-suc zero (neg-int (suc x)) 
    rewrite (r-add-zero {x} ) 
    = 🐓🥚 
int-mul-neg-suc (suc n) (neg-int (suc x)) 
    rewrite (r-add-zero {x} ) 
    = 🐓🥚

int-mul-negzero-ldist : ( p q : Int ) -> ( definition-equal 
                                                            ( int-add ( int-mul (neg-int zero) p ) ( int-mul (neg-int zero) q )) 
                                                            ( int-mul (neg-int zero) (int-add p q) ) 
                                        ) 
int-mul-negzero-ldist (nat-int zero) (nat-int zero) = 🐓🥚
int-mul-negzero-ldist (nat-int zero) (nat-int (suc y)) = 🐓🥚
int-mul-negzero-ldist (nat-int (suc x)) (nat-int zero) 
    rewrite ( r-add-zero {x} ) 
    = 🐓🥚
int-mul-negzero-ldist (nat-int (suc x)) (nat-int (suc y)) 
    rewrite ( suc-skip-add {x} {y} ) 
    = 🐓🥚
int-mul-negzero-ldist (nat-int zero) (neg-int y) = 🐓🥚
int-mul-negzero-ldist (nat-int (suc x)) (neg-int y) 
    rewrite (r-add-zero {y} )     
    = swap-nat-diff-to-int y x    
int-mul-negzero-ldist (neg-int zero) (nat-int zero) = 🐓🥚
int-mul-negzero-ldist (neg-int (suc x)) (nat-int zero) 
    rewrite (r-add-zero {x} ) 
    rewrite ( r-add-zero {x} )
    = 🐓🥚
int-mul-negzero-ldist (neg-int x) (nat-int (suc y)) 
    rewrite (r-add-zero {x} ) 
    = swap-nat-diff-to-int x y
int-mul-negzero-ldist (neg-int x) (neg-int y) 
    rewrite (r-add-zero {x} ) 
    rewrite ( r-add-zero {y} ) 
    rewrite ( r-add-zero {add x y } ) 
    rewrite (suc-skip-add {x} {y} ) 
    = 🐓🥚                                                            

int-mul-neg-ldist : ( n : Nat ) -> ( p q : Int ) 
            -> ( definition-equal ( int-add (int-mul (neg-int n) p) ( int-mul (neg-int n) q) ) 
                                  ( int-mul ( neg-int n ) ( int-add p q ) ) ) 
int-mul-neg-ldist zero p q = int-mul-negzero-ldist p q         
int-mul-neg-ldist (suc n) p q 
    rewrite ( int-mul-neg-suc n p ) 
    rewrite ( int-mul-neg-suc n q ) 
    rewrite ( int-mul-neg-suc n ( int-add p q ) )    
    rewrite ( int-add-ass (int-mul (neg-int 0) p) (int-mul (neg-int n) p)  (int-add (int-mul (neg-int 0) q) (int-mul (neg-int n) q)) )
    rewrite ( sym ( int-add-ass (int-mul (neg-int n) p) (int-mul (neg-int 0) q) (int-mul (neg-int n) q) ) )
    rewrite ( int-add-comm (int-mul (neg-int n) p) (int-mul (neg-int 0) q) )
    rewrite ( int-add-ass (int-mul (neg-int 0) q) (int-mul (neg-int n) p) (int-mul (neg-int n) q))
    rewrite ( sym ( int-add-ass (int-mul (neg-int 0) p) (int-mul (neg-int 0) q) (int-add (int-mul (neg-int n) p) (int-mul (neg-int n) q)) ) )
    rewrite ( int-mul-negzero-ldist p q ) 
    rewrite ( int-mul-neg-ldist n p q ) 
    = 🐓🥚

int-mul-ldist : ( l p q : Int ) -> (definition-equal ( int-add ( int-mul l p ) ( int-mul l q ) ) 
                                                     ( int-mul l ( int-add p q ) ) ) 
int-mul-ldist (nat-int x) p q = int-mul-nat-ldist x p q
int-mul-ldist (neg-int x) p q = int-mul-neg-ldist x p q

int-mul-rdist : ( p q r : Int ) -> ( definition-equal ( int-add ( int-mul p r ) ( int-mul q r ) ) 
                                                      ( int-mul ( int-add p q ) r ) ) 
int-mul-rdist p q r 
    rewrite ( int-mul-comm p r ) 
    rewrite ( int-mul-comm q r ) 
    rewrite ( int-mul-comm (int-add p q) r ) 
    rewrite ( int-mul-ldist r p q ) 
    = 🐓🥚

