module StandardConstructions.Naturals where 

open import StandardConstructions.IdentityType using ( definition-equal; 🐓🥚; cong; sym) 

data Nat : Set where 
    zero : Nat 
    suc : Nat -> Nat 

{-#  BUILTIN NATURAL Nat  #-}

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