--- at first there was nothing
data Empty : Set where 

--- then there was something, the (univalence axiom foreshadowing, in principle "a") one point type 
data Point : Set where 
    pt : Point 

data Nat : Set where 
    zero : Nat 
    suc : Nat -> Nat 

add : Nat -> Nat -> Nat 
add zero m = m
add (suc n) m = suc ( add n m ) 

data Ord : Set where
  zeroOrd : Ord
  sucOrd  : Ord → Ord
  limOrd  : (Nat → Ord) → Ord

open import Level using (Level;_⊔_)

record Irrelevant { a : Level } (A : Set a) : Set a where
  constructor [_]
  field .irrelevant : A

--- universal flying pig which follows from any other contradiction
🐷🛸 : Set
🐷🛸 = Irrelevant Empty

not : Set -> Set 
not A = ( A -> 🐷🛸 )

map-not : { A B : Set } -> ( f : A -> B ) -> ( not B -> not A ) 
map-not f notb a = notb ( f a )

data definition-equal {a} { A : Set a } : A -> A -> Set a where 
    🐓🥚 : { x : A } -> definition-equal x x 

cong : { A B : Set } { x y : A } -> ( f : A -> B ) -> ( definition-equal x y ) -> ( definition-equal ( f x ) ( f y ) ) 
cong f 🐓🥚 = 🐓🥚 

trans : { A : Set } { x y z : A } -> ( definition-equal x y ) -> ( definition-equal y z ) -> ( definition-equal x z ) 
trans 🐓🥚 🐓🥚 = 🐓🥚

eval-equal-maps : { A B : Set } -> { f : A -> B } -> { g : A -> B } -> ( definition-equal f g ) -> ( ( x : A ) -> ( definition-equal ( f x ) ( g x ) ) ) 
eval-equal-maps 🐓🥚 x = 🐓🥚 

{-# BUILTIN EQUALITY definition-equal #-} 

suc-not-eq : { n m : Nat } -> (  definition-equal n m ) -> ( definition-equal ( suc n ) ( suc m ) ) 
suc-not-eq {n = n} {m = m} 🐓🥚 = 🐓🥚

suc-inj : { n m : Nat } -> ( definition-equal ( suc n ) ( suc m ) ) -> ( definition-equal n m ) 
suc-inj {n = n} {m = m} 🐓🥚 = 🐓🥚


data ensemble ( A : Set ) : Set where 
    give-element : A -> ensemble A 

data maps ( A B : Set ) : Set where 
    give-map : ( ensemble A -> ensemble B ) -> maps A B 

data empty ( A : Set ) : Set where 
    prove-empty : maps A Empty -> empty A 

data nonempty ( A : Set ) : Set where 
    prove-nonempty : maps Point A -> nonempty A

id : { A : Set } -> ( A -> A ) 
id = \ x -> x 

id-is-id : { A : Set } { x : A } -> ( definition-equal ( id x ) x ) 
id-is-id = 🐓🥚

circ : { A B C : Set } -> ( B -> C ) -> ( A -> B ) -> ( A -> C ) 
circ g f = \ a -> g ( f a ) 

circ-def : { A B C : Set } -> ( g : B -> C ) -> ( f : A -> B ) -> ( ( a : A ) -> ( definition-equal ( ( circ g f ) a ) ( g ( f a ) ) ) )
circ-def g f a = 🐓🥚

circ-id : { A : Set } -> ( definition-equal ( circ ( id {A} ) ( id {A} ) ) ( id {A} ) ) 
circ-id { A } = 🐓🥚 

promote-map-to-ensemble : { A B : Set } -> ( A -> B ) -> ( ensemble A -> ensemble B ) 
promote-map-to-ensemble f ( give-element a ) = ( give-element ( f a ) )

one-point-set-nonempty : nonempty Point 
one-point-set-nonempty = prove-nonempty ( give-map ( promote-map-to-ensemble ( id { Point } ) ) )

empty-set : empty Empty 
empty-set = prove-empty ( give-map ( promote-map-to-ensemble ( λ () ) ) ) 

standard-empty-reduction : { A : Set } -> empty A -> empty Empty 
standard-empty-reduction empty-proof-A = empty-set

standard-empty-inclusion : { A : Set } -> { empty A } -> empty Empty -> empty A
standard-empty-inclusion { A = A } { empty-proof-A } empty-proof-Empty = empty-proof-A

record PointedSet ( A : Set ) : Set where 
    field 
        set : A 
        chosen-point : Point -> A 

what-s-pointed : { A : Set } -> PointedSet A -> Nat 
what-s-pointed record { set = set ; chosen-point = chosen-point } = zero

PointedNat : Set 
PointedNat = PointedSet Nat 

data Sum ( A B : Set ) : Set where 
    injl : A -> Sum A B 
    injr : B -> Sum A B 

ass-sum : { A B C : Set } -> ( Sum ( Sum A B ) C ) -> ( Sum A ( Sum B C ) ) 
ass-sum (injl (injl x)) = injl x
ass-sum (injl (injr x)) = injr ( injl x )
ass-sum (injr x) = injr ( injr x )

sum-empty-l : { A : Set } -> ( Sum 🐷🛸 A ) -> A 
sum-empty-l (injr x) = x

sum-empty-r : { A : Set } -> ( Sum A 🐷🛸 ) -> A 
sum-empty-r (injl x) = x

sum-empty-l-t : { A : Set } -> A -> ( Sum 🐷🛸 A )
sum-empty-l-t a = injr a

sum-empty-r-t : { A : Set } -> A -> ( Sum A 🐷🛸 )
sum-empty-r-t a = injl a

lneutral-iso0 : { A : Set } -> ( a : A ) -> ( definition-equal ( sum-empty-l ( sum-empty-l-t a ) ) a ) 
lneutral-iso0 a = 🐓🥚

lneutral-iso1 : { A : Set } -> ( z : Sum 🐷🛸 A ) -> ( definition-equal ( sum-empty-l-t ( sum-empty-l z ) )  z ) 
lneutral-iso1 (injr x) = 🐓🥚

twist-sum : { A B : Set } -> ( Sum A B ) -> ( Sum B A ) 
twist-sum (injl x) = injr x
twist-sum (injr x) = injl x

induce-sum-maps : { A B Z : Set } -> ( A -> Z ) -> ( B -> Z ) -> ( Sum A B -> Z ) 
induce-sum-maps f g (injl x) = f x
induce-sum-maps f g (injr x) = g x

record Product ( A B : Set ) : Set where 
    constructor _,_
    field
        p1 : A 
        p2 : B 

open Product public 
infixr 4 _,_

ass-prod : { A B C : Set } -> ( Product ( Product A B ) C ) -> ( Product A ( Product B C ) ) 
ass-prod ( ( a , b ) , c ) = ( a , b , c ) -- infix_R!

prod-point-l : { A : Set } -> ( Product Point A ) -> A 
prod-point-l ( pt , a ) = a

prod-point-r : { A : Set } -> ( Product A Point ) -> A 
prod-point-r ( a , pt ) = a

twist-prod : { A B : Set } -> ( Product A B ) -> ( Product B A ) 
twist-prod ( a , b ) = ( b , a ) 

dist-l : { L A B : Set } -> ( Sum ( Product L A ) ( Product L B ) ) -> ( Product L ( Sum A B ) ) 
dist-l (injl (l , a)) = ( l , injl a )
dist-l (injr (l , b)) = ( l , injr b )

dist-r : { A B R : Set } -> ( Sum ( Product A R ) ( Product B R ) ) -> ( Product ( Sum A B ) R ) 
dist-r (injl (a , r)) = ( injl a , r )
dist-r (injr (b , r)) = ( injr b , r )

induce-product-maps : { A X Y : Set } -> ( A -> X ) -> ( A -> Y ) -> ( A -> Product X Y ) 
induce-product-maps f g a = ( f a , g a ) 

exponential-law : { A B Z : Set } -> ( Product A B -> Z ) -> ( A -> B -> Z ) 
exponential-law f a b = f ( a , b ) 

sum-to-product : { A B : Set } { X Y : Set } { x : X } { y : Y } -> ( A -> X ) -> ( B -> Y ) -> ( Sum A B -> Product X Y ) 
sum-to-product {x = x} {y = y} f g (injl a) = ( f a , y )
sum-to-product {x = x} {y = y} f g (injr b) = ( x , g b )

data Exp ( A B : Set ) : Set where 
    give-map : ( B -> A ) -> Exp A B 

data pointed ( A : Set ) ( a : A ) : Set where 
    is-pointed : A -> pointed A a 

basepoint : { A : Set } { a : A } -> pointed A a -> A
basepoint { a = a } _ = a

data pointed-map ( A : Set ) ( a : A ) ( B : Set ) ( b : B ) : Set where  
    is-pointed-map : ( f : A -> B ) -> { ( definition-equal ( f a ) b ) } -> pointed-map A a B b 

-- the trivial example 
id-pt : pointed-map Point pt Point pt 
id-pt = is-pointed-map id { id-is-id } 

id-nat : pointed-map Nat zero Nat zero 
id-nat = is-pointed-map id { id-is-id } 

{- 
this does not type because the predicate can't be supplied, yum ! :) 
id-nat-wrong : pointed-map Nat zero Nat (suc zero) 
id-nat-wrong = is-pointed-map id { ? }  -}

compose-pointed : { A B C : Set } { a : A } { b : B } { c : C } -> ( f : pointed-map A a B b ) -> ( g : pointed-map B b C c ) -> pointed-map A a C c 
compose-pointed ( is-pointed-map f {predf} ) ( is-pointed-map g {predg} ) = is-pointed-map ( circ g f ) { gpredf }
    where gpredf = trans ( cong g predf ) ( predg ) 

data Fin : Nat -> Set where 
    fzero : ( n : Nat ) -> Fin ( suc n )
    fsucc : ( n : Nat ) -> Fin n -> Fin (suc n) 

fin-family : Nat -> Set 
fin-family zero = 🐷🛸 
fin-family (suc k) = Fin (suc k) 

fin-to-fin-family : ( n : Nat ) -> ( definition-equal ( Fin (suc n ) ) ( fin-family (suc n) ) ) 
fin-to-fin-family n = 🐓🥚

fin-zero-to-empty : ( definition-equal ( fin-family zero ) 🐷🛸 ) 
fin-zero-to-empty = 🐓🥚

two-point-versions-fin-to-pt : Fin ( suc zero ) -> Point 
two-point-versions-fin-to-pt z = pt 

two-point-versions-pt-to-fin : Point -> Fin (suc zero)
two-point-versions-pt-to-fin pt = fzero zero

point-side-inversion : ( x : Point ) -> ( definition-equal ( two-point-versions-fin-to-pt ( two-point-versions-pt-to-fin x ) ) ( id x ) ) 
point-side-inversion pt = 🐓🥚

fin-zero-inversion : ( x : Fin ( suc zero ) ) -> ( definition-equal ( two-point-versions-pt-to-fin ( two-point-versions-fin-to-pt x ) ) ( id x ) ) 
fin-zero-inversion (fzero .zero) = 🐓🥚

-- it is weaker than univalence or similar weaker axioms to assume extensionality, so we will do so 
postulate
  extensionality : {A B : Set} {f g : A -> B}
    -> ((x : A) -> ( definition-equal ( f x ) ( g x ) ))
      -----------------------
    -> ( definition-equal f g )

ext-point-side-inversion : ( definition-equal ( circ two-point-versions-fin-to-pt two-point-versions-pt-to-fin ) id ) 
ext-point-side-inversion = extensionality point-side-inversion

ext-fzero-side-inversion : ( definition-equal ( circ two-point-versions-pt-to-fin two-point-versions-fin-to-pt ) id ) 
ext-fzero-side-inversion = extensionality fin-zero-inversion

ext-lneutral-iso0 : { A : Set } -> ( definition-equal ( circ sum-empty-l sum-empty-l-t ) (id {A}) ) 
ext-lneutral-iso0 = extensionality lneutral-iso0

ext-lneutral-iso1 : { A : Set } -> ( definition-equal ( circ sum-empty-l-t sum-empty-l ) ( id {Sum 🐷🛸 A} ) )
ext-lneutral-iso1 = extensionality lneutral-iso1

data equivalences ( A B : Set ) : Set where 
    prove-equivalence : ( f : A -> B ) -> ( g : B -> A ) -> { definition-equal ( circ f g ) id } -> { definition-equal ( circ g f ) id } -> equivalences A B 

transpose-equivalences : { A B : Set } -> equivalences A B -> equivalences B A 
transpose-equivalences (prove-equivalence f g {predfg} {predgf} ) = prove-equivalence g f {predgf} {predfg}

compose-equivalences : { A B C : Set } -> equivalences A B -> equivalences B C -> equivalences A C 
compose-equivalences { A = A } { B = B } { C = C }
    (prove-equivalence fl gl {lpredfg} {lpredgf}) 
    (prove-equivalence fr gr {rpredfg} {rpredgf}) = prove-equivalence l-to-r-comp r-to-l-comp {lrl-comp} {rlr-comp}
        where l-to-r-comp = \ x -> circ fr fl x 
              r-to-l-comp = \ x -> circ gl gr x 
              
              lpredfg-xd : ( z : B ) -> ( definition-equal ( fl ( gl z ) ) z ) 
              lpredfg-xd = eval-equal-maps lpredfg
              lpredgf-xd : ( z : A ) -> ( definition-equal ( gl ( fl z ) ) z ) 
              lpredgf-xd = eval-equal-maps lpredgf
              rpredfg-xd : ( z : C ) -> ( definition-equal ( fr ( gr z ) ) z ) 
              rpredfg-xd = eval-equal-maps rpredfg
              rpredgf-xd : ( z : B ) -> ( definition-equal ( gr ( fr z ) ) z ) 
              rpredgf-xd = eval-equal-maps rpredgf        

              rlr-def : ( x : C ) -> ( definition-equal ( ( circ l-to-r-comp r-to-l-comp ) x ) ( fr ( fl ( gl ( gr x ) ) ) ) )
              rlr-def x = 🐓🥚
              lrl-def : ( x : A ) -> ( definition-equal ( ( circ r-to-l-comp l-to-r-comp ) x ) ( gl ( gr ( fr ( fl x ) ) ) ) )
              lrl-def x = 🐓🥚

              -- jetzt die vier ausdruecke rechts runterschraben zu x
              frflglgr : ( x : C ) -> ( definition-equal ( fr ( fl ( gl ( gr x ) ) ) ) ( id x ) ) 
              frflglgr x 
                rewrite ( lpredfg-xd ( gr x ) ) 
                rewrite ( rpredfg-xd ( x ) ) 
                = 🐓🥚

              glgrfrfl : ( x : A ) -> ( definition-equal ( gl ( gr ( fr ( fl x ) ) ) ) ( id x ) ) 
              glgrfrfl x 
                rewrite ( rpredgf-xd ( fl x ) ) 
                rewrite ( lpredgf-xd ( x ) ) 
                = 🐓🥚

              lrl-comp : ( definition-equal ( circ l-to-r-comp r-to-l-comp ) id ) 
              lrl-comp = rlr-12
                where rlr-to-comp = extensionality rlr-def 
                      rlr-to-id = extensionality frflglgr 
                      rlr-12 = trans rlr-to-comp rlr-to-id

              rlr-comp : ( definition-equal ( circ r-to-l-comp l-to-r-comp ) id ) 
              rlr-comp = lrl-12
                where lrl-to-comp = extensionality lrl-def
                      lrl-to-id = extensionality glgrfrfl 
                      lrl-12 = trans lrl-to-comp lrl-to-id



incremental-fin : ( n : Nat ) -> ( Sum Point ( Fin n ) -> Fin ( suc n ) ) 
incremental-fin n (injl pt) = fzero n
incremental-fin n (injr x) = fsucc n x

incremental-fin-back : ( n : Nat ) -> ( Fin ( suc n ) -> Sum Point ( Fin n ) ) 
incremental-fin-back n (fzero .n) = injl pt
incremental-fin-back n (fsucc .n z) = injr z

fin-fin-back-id : ( n : Nat ) -> ( z : Sum Point (Fin n ) ) -> ( definition-equal ( incremental-fin-back n ( incremental-fin n z ) ) ( id z ) ) 
fin-fin-back-id n (injl pt) = 🐓🥚
fin-fin-back-id n (injr x) = 🐓🥚

fin-back-fin-id : ( n : Nat ) -> ( z : Fin ( suc n ) ) -> ( definition-equal ( incremental-fin n ( incremental-fin-back n z ) ) ( id z ) ) 
fin-back-fin-id n (fzero .n) = 🐓🥚
fin-back-fin-id n (fsucc .n z) = 🐓🥚

pred-fin-fin-back : { n : Nat } -> ( definition-equal ( circ ( incremental-fin-back n ) ( incremental-fin n ) ) ( id ) ) 
pred-fin-fin-back { n = n } = extensionality ( fin-fin-back-id n ) 

pred-fin-back-fin : { n : Nat } -> ( definition-equal ( circ ( incremental-fin n ) ( incremental-fin-back n ) ) ( id ) ) 
pred-fin-back-fin { n = n } = extensionality ( fin-back-fin-id n ) 

incremental-fin-equivalence : { n : Nat } -> equivalences ( Sum Point (Fin n) ) ( Fin (suc n) )
incremental-fin-equivalence { n = n } = prove-equivalence (incremental-fin n) (incremental-fin-back n) {pred-fin-back-fin} {pred-fin-fin-back}

data has-count ( A : Set ) : Nat -> Set where 
    prove-count : { k : Nat } -> equivalences A ( fin-family k ) -> has-count A k

give-count : { k : Nat } -> ( A : Set ) -> { has-count A k } -> Nat 
give-count { k = k } A = k 

trivial-count : { k : Nat } -> has-count ( fin-family k ) k 
trivial-count {k = k} = prove-count (prove-equivalence id id {circ-id} {circ-id} )

point-is-one : has-count Point (suc zero) 
point-is-one = prove-count (prove-equivalence two-point-versions-pt-to-fin two-point-versions-fin-to-pt {ext-fzero-side-inversion} {ext-point-side-inversion} ) 

data less-than : Nat -> Nat -> Set where 
    gt-zero : { n : Nat } -> ( less-than zero ( suc n ) ) 
    gt-succ : { n m : Nat } -> ( less-than n m ) -> ( less-than ( suc n ) ( suc m ) )  

gt-succ-inv : { n m : Nat } -> ( less-than ( suc n ) ( suc m ) ) -> ( less-than n m ) 
gt-succ-inv (gt-succ pred) = pred

lt-implies-not-equal : ( n m : Nat ) -> ( less-than n m ) -> not (definition-equal n m) 
lt-implies-not-equal zero (suc zero) pred = \ ()
lt-implies-not-equal zero (suc (suc m)) pred = \ ()  
lt-implies-not-equal (suc n) (suc m) (gt-succ pred) = cong-suc ind-step    
    where ind-step = lt-implies-not-equal n m pred 
          cong-suc = map-not suc-inj

lt-trans : ( k l m : Nat ) -> ( less-than k l ) -> ( less-than l m ) -> ( less-than k m ) 
lt-trans zero _ (suc m) gt-zero _ = gt-zero 
lt-trans (suc k) (suc l) (suc m) (gt-succ predkl) (gt-succ predlm) = gt-succ ind-step  
    where ind-step = lt-trans k l m predkl predlm 

lt-implies-not-gt : ( k l : Nat ) -> ( less-than k l ) -> not ( less-than l k ) 
lt-implies-not-gt zero l gt-zero = \ ()
lt-implies-not-gt (suc k) (suc l) (gt-succ pred) = res    
    where ind-step = lt-implies-not-gt k l pred           
          res-map = map-not ( gt-succ-inv { n = l } { m = k } )          
          res = res-map ind-step

asymm-lt : ( n : Nat ) -> not ( less-than n n ) 
asymm-lt zero = \ ()
asymm-lt (suc n) = res
    where ind-step = asymm-lt n 
          res-map = map-not ( gt-succ-inv { n = n } { m = n } )
          res = res-map ind-step

lt-total : ( n m : Nat ) -> Sum ( less-than n m ) ( Sum ( definition-equal n m ) ( less-than m n ) ) 
lt-total zero zero = injr ( injl 🐓🥚 )
lt-total zero (suc m) = injl gt-zero  
lt-total (suc n) zero = injr ( injr gt-zero ) 
lt-total (suc n) (suc m) = res
    where triple-suc : { k l : Nat } 
                    -> Sum ( less-than k l ) ( Sum ( definition-equal k l ) ( less-than l k ) ) 
                    -> Sum ( less-than ( suc k ) ( suc l ) ) ( Sum ( definition-equal ( suc k ) ( suc l ) ) ( less-than ( suc l ) ( suc k ) ) ) 
          triple-suc (injl x) = injl ( gt-succ x )
          triple-suc (injr (injl x)) = injr (injl new-pred)
            where new-pred = ( cong suc ) x 
          triple-suc (injr (injr x)) = injr ( injr ( gt-succ x ) )
          ind-pred = lt-total n m 
          res = triple-suc ind-pred 

data embedding ( A B : Set ) : Set where 
    prove-embedding : ( f : A -> B ) -> ( g : B -> A ) -> { definition-equal ( circ g f ) id } -> embedding A B 

data lteq : Nat -> Nat -> Set where 
    gteq-zero : { n : Nat } -> ( lteq zero n ) 
    gteq-succ : { n m : Nat } -> ( lteq n m ) -> ( lteq (suc n) (suc m) )

lteq-inv : { n m : Nat } -> ( lteq ( suc n ) ( suc m ) ) -> ( lteq n m ) 
lteq-inv (gteq-succ pred) = pred

lteq-disassemble : { n m : Nat } -> ( lteq n m ) -> ( Sum ( less-than n m ) ( definition-equal n m ) )
lteq-disassemble {n = zero} {m = zero} pred = injr 🐓🥚
lteq-disassemble {n = zero} {m = suc m} pred = injl gt-zero  
lteq-disassemble {n = suc n} {m = suc m} (gteq-succ pred) = res 
    where ind-step = lteq-disassemble {n} {m} pred 
          double-step : ( n m : Nat ) 
                     -> ( Sum ( less-than n m ) ( definition-equal n m ) ) 
                     -> ( Sum ( less-than ( suc n ) ( suc m ) ) ( definition-equal ( suc n ) ( suc m ) ) )
          double-step n m (injl x) = injl ( gt-succ x ) 
          double-step n m (injr x) = injr ( ( cong suc ) x )
          res = double-step n m ind-step

lteq-trans : ( k l m : Nat ) -> ( lteq k l ) -> ( lteq l m ) -> ( lteq k m ) 
lteq-trans zero l m gteq-zero predlm = gteq-zero 
lteq-trans (suc k) (suc l) (suc m) predkl predlm = res
    where pre-predkl = lteq-inv predkl 
          pre-predlm = lteq-inv predlm 
          ind-step = lteq-trans k l m pre-predkl pre-predlm          
          res = gteq-succ {k} {m} ind-step 

lteq-antisymm : ( k l : Nat ) -> ( lteq k l ) -> ( lteq l k ) -> ( definition-equal k l ) 
lteq-antisymm zero zero gteq-zero gteq-zero = 🐓🥚 
lteq-antisymm (suc k) (suc l) (gteq-succ predkl) (gteq-succ predlk) = res
    where ind-step = lteq-antisymm k l predkl predlk 
          res = cong suc ( ind-step )

lteq-refl : ( k : Nat ) -> ( lteq k k ) 
lteq-refl zero = gteq-zero 
lteq-refl (suc k) = gteq-succ (lteq-refl k) 

zero-is-not-suc : { k : Nat } -> not ( definition-equal zero ( suc k ) ) 
zero-is-not-suc { k = k } = lt-implies-not-equal zero ( suc k ) gt-zero

nothing-lt-zero : { k : Nat } -> ( less-than k zero) -> 🐷🛸
nothing-lt-zero () 

suc-not-lteq-zero : { k : Nat } -> ( lteq (suc k) zero ) -> 🐷🛸
suc-not-lteq-zero ()

fin1-is-not-fin0 : equivalences ( fin-family (suc zero) ) ( fin-family zero ) -> 🐷🛸
fin1-is-not-fin0 (prove-equivalence f g) = f ( fzero zero )

fin0-is-not-fin1 : equivalences ( fin-family zero ) ( fin-family ( suc zero ) ) -> 🐷🛸
fin0-is-not-fin1 (prove-equivalence f g ) = g ( fzero zero )

sum-point-fin-family : ( k : Nat ) -> ( Sum Point ( fin-family k ) ) -> ( fin-family ( suc k ) ) 
sum-point-fin-family k (injl pt) = fzero k
sum-point-fin-family (suc k) (injr x) = fsucc ( suc k ) x
    
fin-family-sum-point : ( k : Nat ) -> ( fin-family ( suc k ) ) -> ( Sum Point ( fin-family k ) ) 
fin-family-sum-point k (fzero .k) = injl pt  
fin-family-sum-point (suc k) (fsucc .(suc k) z) 
    rewrite ( fin-to-fin-family k ) = injr z 

pt-plus-fin-family-id : ( k : Nat ) -> ( z : Sum Point ( fin-family k ) ) -> ( definition-equal ( fin-family-sum-point k ( sum-point-fin-family k z ) ) z )
pt-plus-fin-family-id zero (injl pt) = 🐓🥚
pt-plus-fin-family-id (suc k) (injl pt) = 🐓🥚
pt-plus-fin-family-id (suc k) (injr x) = 🐓🥚

fin-family-pt-plus-id : ( k : Nat ) -> ( z : ( fin-family ( suc k ) ) ) -> ( definition-equal ( sum-point-fin-family k ( fin-family-sum-point k z ) ) z )
fin-family-pt-plus-id zero (fzero .zero) = 🐓🥚
fin-family-pt-plus-id (suc k) (fzero .(suc k)) = 🐓🥚
fin-family-pt-plus-id (suc k) (fsucc .(suc k) z) = 🐓🥚

ext-pt-fin : { k : Nat } -> ( definition-equal ( circ ( fin-family-sum-point k ) ( sum-point-fin-family k ) ) ( id { Sum Point ( fin-family k ) } ) )
ext-pt-fin { k = k } = extensionality (pt-plus-fin-family-id k)

ext-fin-pt : { k : Nat } -> ( definition-equal ( circ ( sum-point-fin-family k ) ( fin-family-sum-point k ) ) ( id { fin-family ( suc k ) } ) ) 
ext-fin-pt { k = k } = extensionality (fin-family-pt-plus-id k) 

equivalence-pt-sum-fin-family-suc : ( k : Nat ) -> equivalences ( fin-family ( suc k ) ) ( Sum Point ( fin-family k ) ) 
equivalence-pt-sum-fin-family-suc k = prove-equivalence (fin-family-sum-point k) (sum-point-fin-family k) {ext-pt-fin} {ext-fin-pt}   

point-not-empty : not Point -> 🐷🛸
point-not-empty f = f pt 

nnpoint : not ( not Point )
nnpoint = point-not-empty

nnpoint-to-point : not ( not Point ) -> Point 
nnpoint-to-point z = pt 

point-to-nnpoint : Point -> not ( not Point ) 
point-to-nnpoint pt = nnpoint

nnpp-pwise : { x : Point } -> ( definition-equal ( nnpoint-to-point ( point-to-nnpoint x ) ) ( id x ) ) 
nnpp-pwise { x = pt } = 🐓🥚

pnnp-pwise : { x : ( not ( not Point ) ) } -> ( definition-equal ( point-to-nnpoint ( nnpoint-to-point x ) ) ( id x ) ) 
pnnp-pwise { x = z } = 🐓🥚

nnpp-id : ( definition-equal ( circ nnpoint-to-point point-to-nnpoint ) ( id {Point} ) ) 
nnpp-id = extensionality \ x -> nnpp-pwise { x }

pnnp-id : ( definition-equal ( circ point-to-nnpoint nnpoint-to-point ) ( id {not ( not Point ) } ) )
pnnp-id = extensionality \ x -> pnnp-pwise { x }

pt-eq-nnpt : equivalences Point ( not ( not Point ) ) 
pt-eq-nnpt = prove-equivalence point-to-nnpoint nnpoint-to-point {pnnp-id} {nnpp-id}

nnpt-eq-pt : equivalences ( not ( not Point ) ) Point 
nnpt-eq-pt = prove-equivalence nnpoint-to-point point-to-nnpoint {nnpp-id} {pnnp-id}

point-not-empty-eq : equivalences Point 🐷🛸 -> 🐷🛸
point-not-empty-eq (prove-equivalence f g) = f pt

empty-not-point-eq : equivalences 🐷🛸 Point -> 🐷🛸
empty-not-point-eq (prove-equivalence f g) = g pt 

lonely-pig : has-count 🐷🛸 zero 
lonely-pig = prove-count (prove-equivalence id id {🐓🥚}{🐓🥚})

-- if you prove something has no elements, and then give an element, that's a flying pig 
count-zero-implies-not : { A : Set } -> ( has-count A zero ) -> A -> 🐷🛸
count-zero-implies-not (prove-count (prove-equivalence f g)) a = f a 

