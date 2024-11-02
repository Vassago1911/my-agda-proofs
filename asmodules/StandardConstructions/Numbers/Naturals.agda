module StandardConstructions.Numbers.Naturals where 

open import StandardConstructions.AbstractNonsense.IdentityType using ( definition-equal; 🐓🥚; cong; sym; trans) 
open import StandardConstructions.AbstractNonsense.Not using ( 🐷🛸 ) 

data Nat : Set where 
    zero : Nat 
    suc : Nat -> Nat 

{-#  BUILTIN NATURAL Nat  #-}

suc-zero-is-pig : ( n : Nat ) -> ( definition-equal (suc n) zero ) -> 🐷🛸
suc-zero-is-pig n = \ ()

nat-suc-splitter : Nat -> Nat 
nat-suc-splitter zero = zero
nat-suc-splitter (suc n) = n

suc-is-split : ( n : Nat ) -> ( definition-equal ( nat-suc-splitter ( suc n ) ) n ) 
suc-is-split zero = 🐓🥚
suc-is-split (suc n) = 🐓🥚

add : Nat -> Nat -> Nat 
add zero m = m
add (suc n) m = suc ( add n m ) 

mul : Nat -> Nat -> Nat 
mul zero m = zero 
mul ( suc n ) m = ( add m ( mul n m ) ) 

mul-def-reverse : ( n m : Nat ) -> ( definition-equal ( mul ( suc n ) m ) ( add m ( mul n m ) ) )
mul-def-reverse zero m = 🐓🥚
mul-def-reverse (suc n) m = 🐓🥚

exp : Nat -> Nat -> Nat 
exp zero zero = ( suc zero )
exp zero ( suc m ) = zero 
exp (suc m) zero = ( suc zero ) 
exp (suc m) ( suc k ) = ( mul (suc m) ( exp (suc m) k ) ) 

suc-not-eq : { n m : Nat } -> ( definition-equal n m ) -> ( definition-equal ( suc n ) ( suc m ) ) 
suc-not-eq {n = n} {m = m} 🐓🥚 = 🐓🥚

suc-inj : { n m : Nat } -> ( definition-equal ( suc n ) ( suc m ) ) -> ( definition-equal n m ) 
suc-inj {n = n} {m = m} 🐓🥚 = 🐓🥚

add-c-inj : ( c : Nat ) -> ( n m : Nat ) 
        -> ( definition-equal ( add c n ) ( add c m ) ) 
        -> ( definition-equal n m ) 
add-c-inj zero n m pred = pred
add-c-inj (suc c) n m pred     
    = ind-step
    where step = suc-inj {add c n} {add c m} pred 
          ind-step = add-c-inj c n m step 
    
l-add-zero : { n : Nat } -> ( definition-equal ( add zero n ) n ) 
l-add-zero { n = n } = 🐓🥚

r-add-zero : { n : Nat } -> ( definition-equal ( add n zero ) n ) 
r-add-zero {n = zero} = 🐓🥚
r-add-zero {n = suc n} = cong suc (r-add-zero {n})

l-add-one-suc : { n : Nat } -> ( definition-equal ( add ( suc zero ) n ) ( suc n ) ) 
l-add-one-suc {n = zero} = 🐓🥚
l-add-one-suc {n = suc n} = 🐓🥚

r-add-one-suc : { n : Nat } -> ( definition-equal ( add n ( suc zero ) ) ( suc n ) ) 
r-add-one-suc {n = zero} = 🐓🥚
r-add-one-suc {n = suc n} = cong suc (r-add-one-suc {n})

suc-add-def : ( n m : Nat ) -> ( definition-equal ( suc ( add n m ) ) ( add ( suc n ) m ) ) 
suc-add-def n m = 🐓🥚

suc-skip-add : { n m : Nat } -> ( definition-equal ( add n ( suc m ) ) ( add ( suc n ) m ) ) 
suc-skip-add {n = zero} {m = m} = 🐓🥚
suc-skip-add {n = suc n} {m = m } = cong suc ind-step
    where ind-step = suc-skip-add { n } { m } 

add-comm : { n m : Nat } -> ( definition-equal ( add n m ) ( add m n ) ) 
add-comm {n = zero} {m = zero} = 🐓🥚
add-comm {n = zero} {m = suc m} = cong suc ( sym ( r-add-zero ) )
add-comm {n = suc n} {m = zero} = cong suc ( r-add-zero )
add-comm {n = suc n} {m = suc m} 
    rewrite ( suc-skip-add { n } { m } ) 
    rewrite ( suc-skip-add { m } { n } ) 
    = cong suc (cong suc (add-comm { n } { m }))

add-ass : { k l m : Nat } -> ( definition-equal ( add ( add k l ) m ) ( add k ( add l m ) ) )
add-ass {k = zero} {l = l} {m = m} = 🐓🥚
add-ass {k = suc k} {l = l} {m = m} = cong suc (add-ass { k } { l } { m })

add-inj : { a b k : Nat } -> ( definition-equal ( add a k ) ( add b k ) ) -> ( definition-equal a b ) 
add-inj {a = a} {b = b} {k = zero} pred 
    rewrite ( r-add-zero { a } ) 
    rewrite ( r-add-zero { b } ) 
    = pred
add-inj {a = a} {b = b} {k = suc k} pred 
    rewrite ( suc-skip-add { a } { k } ) 
    rewrite ( suc-skip-add { b } { k } )     
    = res    
    where ind-step = add-inj { a } { b } { k } 
          downto-ind = suc-inj { add a k } { add b k } pred 
          res = ind-step downto-ind

l-zero-absorbs : { a : Nat } -> ( definition-equal ( mul zero a ) zero ) 
l-zero-absorbs {zero} = 🐓🥚
l-zero-absorbs {suc a} = 🐓🥚

r-zero-absorbs : { a : Nat } -> ( definition-equal ( mul a zero ) zero ) 
r-zero-absorbs {zero} = 🐓🥚
r-zero-absorbs {suc a} = ind-step 
    where ind-step = r-zero-absorbs { a } 

l-one-neutral : { a : Nat } -> ( definition-equal ( mul ( suc zero ) a ) a ) 
l-one-neutral {zero} = 🐓🥚
l-one-neutral {suc a} = cong suc (r-add-zero {a})

r-one-neutral : { a : Nat } -> ( definition-equal ( mul a ( suc zero ) ) a ) 
r-one-neutral {zero} = 🐓🥚
r-one-neutral {suc a} = cong suc (r-one-neutral {a})

mul-comm : { k l : Nat } -> ( definition-equal ( mul k l ) ( mul l k ) ) 
mul-comm {zero} {zero} = 🐓🥚
mul-comm {zero} {suc l} 
    rewrite ( r-zero-absorbs { l } )
    = 🐓🥚
mul-comm {suc k} {zero} 
    rewrite ( r-zero-absorbs { k } ) 
    = 🐓🥚
mul-comm {suc k} {suc l} 
    rewrite ( mul-comm { k } { suc l } ) 
    rewrite ( mul-comm { l } { suc k } ) 
    rewrite ( mul-comm { l } { k } ) 
    rewrite ( sym ( add-ass { l } { k } { mul k l } ) )
    rewrite ( sym ( add-ass { k } { l } { mul k l } ) ) 
    rewrite ( add-comm { k } { l } )
    = cong suc 🐓🥚 

mul-def-reverse1 : ( n m : Nat ) -> ( definition-equal ( mul n ( suc m ) ) ( add n ( mul n m ) ) )
mul-def-reverse1 n zero 
    rewrite ( r-one-neutral { n } ) 
    rewrite ( r-zero-absorbs { n } ) 
    rewrite ( r-add-zero { n } ) 
    = 🐓🥚
mul-def-reverse1 zero (suc m) = 🐓🥚
mul-def-reverse1 (suc n) (suc m)     
    rewrite ( mul-comm { n } { suc ( suc m ) } )
    rewrite ( mul-comm { n } { suc m } ) 
    rewrite ( suc-skip-add { n } { (add m (add n (mul m n))) } ) 
    rewrite ( sym ( add-ass { m } { n } { (add n (mul m n)) } ) )
    rewrite ( sym ( add-ass { n } { m } { (add n (mul m n)) } ) ) 
    rewrite ( add-comm { n } { m } ) 
    = cong suc (cong suc 🐓🥚)
    
ldist-mul : { l a b : Nat } -> ( definition-equal ( add ( mul l a ) ( mul l b ) ) ( mul l ( add a b ) ) ) 
ldist-mul {zero} {a} {b} = 🐓🥚
ldist-mul {suc l} {a} {b} 
    rewrite ( sym  ( add-ass { add a ( mul l a ) }  { b } {  mul l b } ) )
    rewrite ( add-ass { a } { mul l a } { b } ) 
    rewrite ( add-comm { mul l a } { b } ) 
    rewrite ( sym ( add-ass { a } { b } { mul l a } ) )
    rewrite ( add-ass { add a b } { mul l a } { mul l b } ) 
    rewrite ( ldist-mul {l} {a} {b} ) 
    = 🐓🥚

rdist-mul : { a b r : Nat } -> ( definition-equal ( add ( mul a r ) ( mul b r ) ) ( mul ( add a b ) r ) ) 
rdist-mul { a } { b } { r } 
    rewrite ( mul-comm { a } { r } ) 
    rewrite ( mul-comm { b } { r } ) 
    rewrite ( mul-comm { add a b } { r } ) 
    rewrite ( ldist-mul { r } { a } { b } ) 
    = 🐓🥚

mul-ass : { a b c : Nat } -> ( definition-equal ( mul ( mul a b ) c ) ( mul a ( mul b c ) ) ) 
mul-ass {zero} {b} {c} = 🐓🥚
mul-ass {suc a} {b} {c} 
    rewrite ( sym ( rdist-mul { b } { mul a b } { c } ) ) 
    rewrite ( mul-ass { a } { b } { c } ) 
    = 🐓🥚

power-zero : { a : Nat } -> ( definition-equal ( exp a zero ) ( suc zero ) )
power-zero {zero} = 🐓🥚
power-zero {suc a} = 🐓🥚

power-one : { a : Nat } -> ( definition-equal ( exp a ( suc zero ) ) a ) 
power-one {zero} = 🐓🥚
power-one {suc a} = cong suc (r-one-neutral {a})

one-powers : { a : Nat } -> ( definition-equal ( exp ( suc zero ) a ) ( suc zero ) ) 
one-powers {zero} = 🐓🥚
one-powers {suc a} 
    rewrite ( r-add-zero {(exp (suc zero) a) } ) 
    = one-powers {a}

power-suc : { a k : Nat } -> ( definition-equal ( exp a ( suc k ) ) ( mul a ( exp a k ) ) )
power-suc {zero} {zero} = 🐓🥚
power-suc {zero} {suc k} = 🐓🥚
power-suc {suc a} {zero} = 🐓🥚
power-suc {suc a} {suc k} = 🐓🥚

power-suc-1 : { a k l : Nat } -> ( definition-equal ( exp a ( add k (suc l) ) ) ( mul a ( exp a ( add k l ) ) ) )
power-suc-1 {a} {k} {zero} 
    rewrite ( r-add-zero { k } ) 
    rewrite ( add-comm { k } { suc zero } ) 
    rewrite ( power-suc { a } { k } )
    = 🐓🥚 
power-suc-1 {a} {k} {suc l} 
    rewrite ( add-comm { k } { suc ( suc l ) } ) 
    rewrite ( add-comm { k } { suc l } ) 
    rewrite ( power-suc { a } { suc (add l k ) } )     
    = 🐓🥚

power-suc-2 : { a k l : Nat } -> ( definition-equal ( exp a ( add (suc k ) l ) ) ( mul a ( exp a ( add k l ) ) ) ) 
power-suc-2 {a} {k} {l}     
    rewrite ( power-suc {a} { add k l } ) 
    = 🐓🥚

exponent-addition : { a k l : Nat } -> ( definition-equal ( mul ( exp a k ) ( exp a l ) ) ( exp a ( add k l ) ) )
exponent-addition {a} {k} {zero} 
    rewrite ( power-zero {a} ) 
    rewrite ( r-one-neutral { exp a k } ) 
    rewrite ( r-add-zero { k} ) 
    = 🐓🥚 
exponent-addition {a} {k} {suc l} 
    rewrite ( add-comm {k} {suc l} )
    rewrite ( power-suc {a} { l } ) 
    rewrite ( power-suc { a } { add l k } ) 
    rewrite ( sym ( mul-ass {exp a k } {a} {exp a l} ) )
    rewrite ( mul-comm {exp a k} {a} ) 
    rewrite ( mul-ass { a } { exp a k } { exp a l } ) 
    rewrite ( exponent-addition { a } { k } { l } ) 
    rewrite ( add-comm {l} {k} )
    = 🐓🥚

data Pos : Set where 
    p1 : Nat -> Pos 

pos-add : Pos -> Pos -> Pos 
pos-add (p1 x) (p1 y) = p1 ( suc (add x y ) )

pos-add-ass : ( x y z : Pos ) -> ( definition-equal ( pos-add ( pos-add x y ) z ) ( pos-add x ( pos-add y z ) ) ) 
pos-add-ass (p1 x) (p1 y) (p1 z) 
    rewrite ( suc-skip-add {x} {add y z} ) 
    rewrite ( add-ass {x} {y} {z} ) 
    = 🐓🥚

pos-add-comm : ( x y : Pos ) -> ( definition-equal ( pos-add x y ) ( pos-add y x ) ) 
pos-add-comm (p1 x) (p1 y) 
    rewrite ( add-comm {x} {y} )
    = 🐓🥚

pos-add-one : ( x : Nat ) -> ( definition-equal ( pos-add (p1 zero) (p1 x) ) (p1 (suc x)) )
pos-add-one x = 🐓🥚

pos-one-add : ( x : Nat ) -> ( definition-equal ( pos-add (p1 x) (p1 zero) ) (p1 (suc x)) )
pos-one-add zero = 🐓🥚
pos-one-add (suc x) 
    rewrite ( r-add-zero {x} ) 
    = 🐓🥚

pos-to-posnat : Pos -> Nat 
pos-to-posnat (p1 x) = suc x

nat-to-pos : Nat -> Pos 
nat-to-pos zero = p1 zero 
nat-to-pos (suc x) = p1 x 

pnp : ( p : Pos ) -> ( definition-equal ( nat-to-pos ( pos-to-posnat p ) ) p ) 
pnp (p1 x) = 🐓🥚

npn : ( n : Nat ) -> ( definition-equal ( pos-to-posnat ( nat-to-pos (suc n ) ) ) (suc n ) ) 
npn n = 🐓🥚

pos-mul : Pos -> Pos -> Pos 
pos-mul (p1 p) (p1 q) = nat-to-pos ( mul ( pos-to-posnat (p1 p) ) ( pos-to-posnat (p1 q) ) ) 

pos-mul-lunital : ( p : Pos ) -> ( definition-equal (pos-mul (p1 zero) p ) p ) 
pos-mul-lunital (p1 zero) = 🐓🥚 
pos-mul-lunital (p1 (suc x)) 
    rewrite ( r-add-zero {x} )
    = 🐓🥚

pos-mul-runital : ( p : Pos ) -> ( definition-equal (pos-mul p ( p1 zero ) ) p ) 
pos-mul-runital (p1 zero) = 🐓🥚 
pos-mul-runital (p1 (suc x)) 
    rewrite ( r-one-neutral {x} ) 
    = 🐓🥚

p1-hom : ( p q : Pos ) 
    -> ( definition-equal 
            ( mul (pos-to-posnat p ) ( pos-to-posnat q ) ) 
            ( pos-to-posnat ( pos-mul p q ) ) ) 
p1-hom (p1 x) (p1 y) = 🐓🥚

pos-to-pred-nat : Pos -> Nat 
pos-to-pred-nat (p1 x) = x

p1-inj : ( n m : Nat ) -> ( definition-equal ( p1 n ) ( p1 m ) ) -> ( definition-equal n m ) 
p1-inj n m pred 
    rewrite ( cong pos-to-pred-nat pred ) 
    = 🐓🥚

np-hom : ( n m : Nat ) 
    -> ( definition-equal
            ( pos-mul ( nat-to-pos (suc n) ) ( nat-to-pos (suc m) ) ) 
            ( nat-to-pos ( mul (suc n) (suc m) ) ) ) 
np-hom zero m = 🐓🥚 
np-hom (suc n) m = 🐓🥚

sympnp : ( p : Pos ) -> ( definition-equal p ( nat-to-pos ( pos-to-posnat p ) ) ) 
sympnp p = sym ( pnp p )

pnpmul : ( p q : Pos ) -> ( definition-equal ( pos-mul p q ) ( nat-to-pos ( pos-to-posnat ( pos-mul p q ) ) ) ) 
pnpmul p q = sympnp ( pos-mul p q ) 

pnpmul-to-natmul : ( p q : Pos ) -> ( definition-equal ( pos-mul p q ) ( nat-to-pos ( mul ( pos-to-posnat p ) ( pos-to-posnat q ) ) ) ) 
pnpmul-to-natmul (p1 x) (p1 y) = 🐓🥚

pnpmulass-to-natmul : ( p q r : Pos ) 
            -> ( definition-equal 
                    ( pos-mul ( pos-mul p q ) r ) 
                    ( nat-to-pos
                        ( mul 
                            ( mul ( pos-to-posnat p ) 
                                  ( pos-to-posnat q ) ) 
                            ( pos-to-posnat r ) ) ) ) 
pnpmulass-to-natmul (p1 x) (p1 y) (p1 z) = 🐓🥚

pnpmulass-to-natmulrass : ( p q r : Pos ) 
            -> ( definition-equal 
                    ( pos-mul ( pos-mul p q ) r ) 
                    ( nat-to-pos
                        ( mul 
                            ( pos-to-posnat p ) 
                            ( mul ( pos-to-posnat q )  
                                  ( pos-to-posnat r ) ) ) ) )
pnpmulass-to-natmulrass p q r 
    rewrite ( pnpmulass-to-natmul p q r ) 
    rewrite ( mul-ass {pos-to-posnat p} {pos-to-posnat q} {pos-to-posnat r} ) 
    = 🐓🥚

pnpmul-to-pnprassmul : ( p q r : Pos ) 
            -> ( definition-equal
                    ( pos-mul p ( pos-mul q r ) ) 
                    ( nat-to-pos
                        ( mul 
                            ( pos-to-posnat p ) 
                            ( mul ( pos-to-posnat q )  
                                  ( pos-to-posnat r ) ) ) ) )
pnpmul-to-pnprassmul (p1 x) (p1 y) (p1 z) = 🐓🥚

posmul-ass : ( p q r : Pos ) 
        -> ( definition-equal 
                ( pos-mul ( pos-mul p q ) r ) 
                ( pos-mul p ( pos-mul q r ) ) )
posmul-ass p q r 
    rewrite ( pnpmul-to-pnprassmul p q r ) 
    rewrite ( sym ( pnpmulass-to-natmulrass p q r ) )     
    = 🐓🥚

posmul-comm : ( p q : Pos ) 
        -> ( definition-equal 
                ( pos-mul p q ) 
                ( pos-mul q p ) ) 
posmul-comm p q 
    rewrite ( pnpmul-to-natmul p q ) 
    rewrite ( mul-comm {pos-to-posnat p} {pos-to-posnat q} ) 
    rewrite ( sym ( pnpmul-to-natmul q p ) ) 
    = 🐓🥚
 
nat-add-mul-lemma : ( n m : Nat ) 
    -> ( definition-equal 
            ( suc ( add n ( mul m (suc n) ) )  )
            ( mul ( suc m ) ( suc n ) ) ) 
nat-add-mul-lemma n m = 🐓🥚            

add-pumping : ( n m : Nat ) ->  ( definition-equal ( add n m ) zero ) -> ( definition-equal n zero ) 
add-pumping zero m pred = 🐓🥚

nat-mul-no-zero-div : ( n m : Nat ) 
        -> ( definition-equal ( mul ( suc n ) m ) zero ) 
        -> ( definition-equal m zero ) 
nat-mul-no-zero-div n m pred = add-pumping m (mul n m) pred        

mul-suc-inj-at-zero : ( p : Nat ) -> ( n : Nat ) 
            -> ( definition-equal ( mul (suc p) n ) zero ) -> ( definition-equal n zero ) 
mul-suc-inj-at-zero zero n pred 
    rewrite ( r-add-zero {n} ) 
    = pred
mul-suc-inj-at-zero (suc p) n pred = add-pumping n (add n (mul p n)) pred

mul-sucs-not-zero : ( n m : Nat ) -> ( definition-equal ( mul ( suc n ) ( suc m ) ) zero ) -> 🐷🛸
mul-sucs-not-zero zero zero ()
mul-sucs-not-zero zero (suc m) ()  
mul-sucs-not-zero (suc n) m () 

one : Pos 
one = p1 zero 

posmul-one-neutral : ( p : Pos ) -> ( definition-equal ( pos-mul one p ) p ) 
posmul-one-neutral (p1 x) 
   rewrite ( r-add-zero {x} ) 
   = 🐓🥚

posmul-ldist-step : ( x : Nat ) -> ( p : Pos ) 
   -> ( definition-equal
         ( pos-mul ( p1 (suc x) ) p ) 
         ( pos-add p ( pos-mul (p1 x) p ) ) ) 
posmul-ldist-step zero (p1 x) 
   rewrite ( suc-skip-add {x} {(add x zero)} ) 
   = 🐓🥚
posmul-ldist-step (suc x) (p1 y) 
   rewrite ( suc-skip-add {y} {(add y (suc (add y (mul x (suc y)))))} ) 
   = 🐓🥚         

pos-mul-ldist : ( l p q : Pos ) 
             -> ( definition-equal
                    ( pos-add ( pos-mul l p ) ( pos-mul l q ) ) 
                    ( pos-mul l ( pos-add p q ) ) ) 
pos-mul-ldist (p1 zero) (p1 y) (p1 z) 
   rewrite ( r-add-zero {y} ) 
   rewrite ( r-add-zero {z} ) 
   rewrite ( r-add-zero {add y z} ) 
   = 🐓🥚 
pos-mul-ldist (p1 (suc x)) (p1 zero) (p1 z) 
   rewrite ( suc-skip-add {z} {(suc (add z (mul x (suc (suc z)))))} )
   rewrite ( r-one-neutral {x} ) 
   rewrite ( suc-skip-add {z} { add z (mul x (suc (suc z))) } ) 
   rewrite ( suc-skip-add {z} { add z (mul x (suc z)) } ) 
   rewrite ( suc-skip-add {x} { (add z (add z (mul x (suc z)))) } ) 
   rewrite (sym ( add-ass {x} {z} {add z (mul x (suc z))} ) )
   rewrite ( add-comm {x} {z} ) 
   rewrite ( add-ass {z} {x} {add z (mul x (suc z))} )
   rewrite (sym ( add-ass {x} {z} {mul x (suc z)} ) )
   rewrite ( add-comm {x} {z} )
   rewrite ( add-ass {z} {x} {mul x (suc z)} )    
   rewrite ( mul-def-reverse1 x (suc z) ) 
   = 🐓🥚
pos-mul-ldist (p1 (suc x)) (p1 (suc y)) (p1 zero) 
   rewrite ( r-add-zero {y} ) 
   rewrite ( r-one-neutral {x} ) 
   rewrite ( add-ass {y} {  (suc (suc (add y (mul x (suc (suc y)))))) } {suc x} )
   rewrite ( suc-skip-add { add y (mul x (suc (suc y))) } { x } ) 
   rewrite ( add-ass {y} {mul x (suc (suc y)) } {x} ) 
   rewrite ( add-comm {mul x (suc (suc y) ) } {x} ) 
   rewrite ( mul-def-reverse1 x (suc (suc y) ) ) 
   = 🐓🥚
pos-mul-ldist (p1 (suc x)) (p1 (suc y)) (p1 (suc z)) 
   rewrite ( add-ass {y} {suc z} {mul (suc x) (suc (suc (suc (add y (suc z)))))} ) 
   rewrite ( add-ass {y} {suc (suc (add y (mul x (suc (suc y))))) } {suc (add z (suc (suc (add z (mul x (suc (suc z)))))))} )
   rewrite ( suc-skip-add {z} { suc (suc (add (add y (suc z)) (mul x (suc (suc (suc (add y (suc z)))))))) } ) 
   rewrite ( suc-skip-add {add y (mul x (suc (suc y))) } { (add z (suc (suc (add z (mul x (suc (suc z))))))) } ) 
   rewrite ( suc-skip-add {z} {(suc (add (add y (suc z)) (mul x (suc (suc (suc (add y (suc z)))))))) } )   
   rewrite ( add-comm {(add y (mul x (suc (suc y))))} { add z (suc (suc (add z (mul x (suc (suc z)))))) } ) 
   rewrite ( add-ass {z} {(suc (suc (add z (mul x (suc (suc z))))))} {(add y (mul x (suc (suc y))))} )
   rewrite ( suc-skip-add {y} {z}) 
   rewrite ( add-ass {z} {(mul x (suc (suc z)))} {(add y (mul x (suc (suc y))))} )
   rewrite ( sym ( add-ass {mul x (suc (suc z))} {y} {mul x (suc (suc y))} ) )
   rewrite ( add-comm {(mul x (suc (suc z)))} {y} )
   rewrite ( add-ass {y} {(mul x (suc (suc z)))} {mul x (suc (suc y))} )
   rewrite ( sym ( add-ass {z} {y} {(add (mul x (suc (suc z))) (mul x (suc (suc y))))} ) )
   rewrite ( add-comm {z} {y} ) 
   rewrite ( ldist-mul {x} {suc (suc z)} {suc (suc y)} )
   rewrite ( suc-skip-add {z} {(suc y)} ) 
   rewrite ( suc-skip-add {z} {y})
   rewrite ( add-comm {z} {y} ) 
   = 🐓🥚

pos-mul-rdist : ( p q r : Pos ) 
            -> ( definition-equal 
                    ( pos-add ( pos-mul p r ) ( pos-mul q r ) ) 
                    ( pos-mul ( pos-add p q ) r ) ) 
pos-mul-rdist p q r 
   rewrite ( posmul-comm p r ) 
   rewrite ( posmul-comm q r ) 
   rewrite ( posmul-comm (pos-add p q) r ) 
   rewrite ( pos-mul-ldist r p q )    
   = 🐓🥚

pos-mul3 : Pos -> Pos -> Pos -> Pos 
pos-mul3 p q r = ( pos-mul p ( pos-mul q r ) ) 

pos-mul3-lass : ( p q r : Pos ) -> ( definition-equal ( pos-mul ( pos-mul p q ) r ) ( pos-mul3 p q r ) ) 
pos-mul3-lass p q r 
   rewrite ( posmul-ass p q r ) 
   = 🐓🥚

add-inj-lemma : ( x y : Nat ) -> ( definition-equal ( add x x ) ( add y y ) ) -> ( definition-equal x y ) 
add-inj-lemma zero zero pred = 🐓🥚
add-inj-lemma (suc x) (suc y) pred 
    rewrite (suc-skip-add {x} {x} ) 
    rewrite ( suc-skip-add {y} {y} ) 
    = res
    where step = suc-inj {(suc (add x x))} {(suc (add y y))} pred 
          step1 = suc-inj {add x x} {add y y} step 
          res = cong suc ( add-inj-lemma x y step1 )
    
