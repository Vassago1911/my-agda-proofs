data definition-equal {a} { A : Set a } : A -> A -> Set a where 
    🐓🥚 : { x : A } -> definition-equal x x 

cong : { A B : Set } { x y : A } -> ( f : A -> B ) -> ( definition-equal x y ) -> ( definition-equal ( f x ) ( f y ) ) 
cong f 🐓🥚 = 🐓🥚 

{-# BUILTIN EQUALITY definition-equal #-} 

data Empty : Set where 

--- then there was something, the (univalence axiom foreshadowing, in principle "a") one point type 
data Point : Set where 
    pt : Point 

open import Level using (Level;_⊔_)

record Irrelevant { a : Level } (A : Set a) : Set a where
  constructor [_]
  field .irrelevant : A

--- universal flying pig which follows from any other contradiction
🐷🛸 : Set
🐷🛸 = Irrelevant Empty

--- A is not satisfied, if it implies the existence of a flying pig 
not : Set -> Set 
not A = ( A -> 🐷🛸 )

apply-notty-element : { A : Set } -> not A -> A -> 🐷🛸
apply-notty-element not-a a = not-a a  

initial-map : { A : Set } -> ( 🐷🛸 -> A ) 
initial-map = \ () 

data Nat : Set where 
    zero : Nat
    suc : Nat -> Nat 

add : Nat -> Nat -> Nat 
add zero m = m
add (suc n) m = suc ( add n m )

add-zero-lneutral : ( n : Nat ) -> ( definition-equal ( add zero n ) n ) 
add-zero-lneutral n = 🐓🥚

add-zero-rneutral : ( n : Nat ) -> ( definition-equal ( add n zero ) n ) 
add-zero-rneutral zero = 🐓🥚
add-zero-rneutral (suc n) 
    rewrite ( add-zero-rneutral n ) = 🐓🥚

add-one-is-suc : ( n : Nat ) -> ( definition-equal ( add n ( suc zero ) ) ( suc n ) )
add-one-is-suc zero = 🐓🥚
add-one-is-suc (suc n) = cong suc (( add-one-is-suc n ))

one-add-is-suc : ( n : Nat ) -> ( definition-equal ( suc n )  ( add ( suc zero ) n )  )
one-add-is-suc n = 🐓🥚

data less-than : Nat -> Nat -> Set where 
    gt-zero : ( n : Nat ) -> ( less-than zero (suc n) )
    gt-suc : ( n m : Nat ) -> ( less-than n m ) -> ( less-than (suc n) (suc m) )

lt-suc-inv : ( n m : Nat ) -> ( less-than ( suc n ) ( suc m ) ) -> ( less-than n m )
lt-suc-inv n m (gt-suc .n .m pred) = pred

nothing-less-than-zero : ( n : Nat ) -> ( not ( less-than n zero ) ) 
nothing-less-than-zero n = \ ()

lt-irreflexive : ( n : Nat ) -> ( not ( less-than n n ) ) 
lt-irreflexive zero = λ ()
lt-irreflexive (suc n) x = nn-pig one-down
    where one-down = lt-suc-inv n n x 
          nn-pig = lt-irreflexive n 

lt-irr1 : ( n m : Nat ) -> ( definition-equal n m ) -> ( not ( less-than n m ) ) 
lt-irr1 n m pred 
    rewrite pred 
    = lt-irreflexive m

lt-transitive : ( l m n : Nat ) -> ( less-than l m ) -> ( less-than m n ) -> ( less-than l n ) 
lt-transitive zero (suc m) (suc n) (gt-zero .m) (gt-suc .m .n predmn) = ( gt-zero n )
lt-transitive (suc l) (suc m) (suc n) (gt-suc .l .m predlm) (gt-suc .m .n predmn) = gt-suc l n ind-step
    where ind-step = lt-transitive l m n predlm predmn           

all-lt-suc : ( n : Nat ) -> ( less-than n (suc n) ) 
all-lt-suc zero = gt-zero zero 
all-lt-suc (suc n) = ind-step
    where ind-step = gt-suc n (suc n) (all-lt-suc n)

lt-asymm : ( n m : Nat ) -> ( less-than n m ) -> ( not ( less-than m n ) ) 
lt-asymm n m pred predinv = middle-pig
    where middle-lt = lt-transitive m n m predinv pred 
          middle-pig = ( lt-irreflexive m ) middle-lt

suc-monotonic : ( n m : Nat ) -> ( less-than n m ) -> ( less-than ( suc n ) ( suc m ) ) 
suc-monotonic n m pred = gt-suc n m pred

data triple-sum ( A B C : Set ) : Set where 
    inj-a : A -> triple-sum A B C
    inj-b : B -> triple-sum A B C
    inj-c : C -> triple-sum A B C 

red-a : { A B C : Set } -> ( a : A ) -> triple-sum A B C -> A 
red-a a (inj-a x) = x
red-a a (inj-b x) = a
red-a a (inj-c x) = a

red-b : { A B C : Set } -> ( b : B ) -> triple-sum A B C -> B 
red-b b (inj-a x) = b
red-b b (inj-b x) = x
red-b b (inj-c x) = b

red-c : { A B C : Set } -> ( c : C ) -> triple-sum A B C -> C 
red-c c (inj-a x) = c
red-c c (inj-b x) = c
red-c c (inj-c x) = x

-- the red's provide retractions for non-empty summands 
-- hence the inj's are provably monic circ definition-equal all that 

-- now we'd like the summands to be disjoint, i.e. given a : A, b : B and a predicate ( definition-equal ( inj-a a ) ( inj-b b ) ) 
-- get a flying pig 🐷🛸 

sum-lm-summands-disjoint : { A B C : Set } ( a : A ) -> ( b : B ) -> ( not ( definition-equal ( inj-a {C = C} a ) ( inj-b {C = C} b ) ) )
sum-lm-summands-disjoint a b = λ ()

sum-lr-summands-disjoint : { A B C : Set } ( b : B ) -> ( c : C ) -> ( not ( definition-equal ( inj-b {A = A} b ) ( inj-c {A = A} c ) ) )
sum-lr-summands-disjoint a b = λ ()

sum-mr-summands-disjoint : { A B C : Set } ( a : A ) -> ( c : C ) -> ( not ( definition-equal ( inj-c {B = B} c ) ( inj-a {B = B} a ) ) )
sum-mr-summands-disjoint a b = λ ()

triple-fun : { A B C D E F : Set } 
          -> ( f : A -> B ) -> ( g : C -> D ) -> ( h : E -> F ) 
          -> ( ( triple-sum A C E ) -> ( triple-sum B D F ) ) 
triple-fun f g h (inj-a x) = inj-a (f x)
triple-fun f g h (inj-b x) = inj-b (g x) 
triple-fun f g h (inj-c x) = inj-c (h x)

triple-step : ( n m : Nat ) 
           -> ( triple-sum ( less-than n m ) ( definition-equal n m ) ( less-than m n ) ) 
           -> ( triple-sum ( less-than ( suc n ) ( suc m ) ) ( definition-equal ( suc n ) ( suc m ) ) ( less-than ( suc m ) ( suc n ) ) ) 
triple-step n m (inj-a x) = inj-a ( gt-suc n m x )
triple-step n m (inj-b x) = inj-b ( cong suc x )
triple-step n m (inj-c x) = inj-c ( gt-suc m n x )

lt-total : ( n m : Nat ) -> ( triple-sum ( less-than n m ) ( definition-equal n m ) ( less-than m n ) )
lt-total zero zero = inj-b 🐓🥚
lt-total zero (suc m) = inj-a ( gt-zero m )  
lt-total (suc n) zero = inj-c ( gt-zero n) 
lt-total (suc n) (suc m) = ind-step
    where ind-step = triple-step n m ( lt-total n m )

-- and with summands are disjoint from above, we can always cook down the number of summands 
-- "without loss of generality n < m" .. i.e. autoprove the n > m case 
-- .. but, there's nothing special about less-than, B can be any doubly naturally indexed type 
wlog-nltm : { A : Set } { B : Nat -> Nat -> Set } -> ( ( n m : Nat ) -> ( B n m ) -> A ) -> ( ( n m : Nat ) -> ( B m n ) -> A )
wlog-nltm amap n m pred = amap m n pred 

-- so this works for B = less-than, and would work for a sum type B = definition-equal | less-than we won't define 

-- but in particular the trichotomy should imply, that having a map ( n m : Nat ) -> ( less-than n m ) -> A 
-- is the same thing as a map Nat -> A  ---   i.e. there should be a homotopy equivalence here?
-- a retraction of a lt-pred map onto a simply inductive one, and the other direction is just an inclusion
retract-orderly-map : { A : Set } -> ( ( n m : Nat ) -> ( less-than n m ) -> A ) -> ( Nat -> A ) 
retract-orderly-map amap n = amap n (suc n) ( all-lt-suc n ) 

retract-def-lemma : { A : Set } 
                 -> ( g : ( n m : Nat ) -> ( less-than n m ) -> A ) 
                 -> ( ( n : Nat ) -> ( definition-equal ( ( retract-orderly-map g ) n ) ( g n (suc n) (all-lt-suc n) )  ) )
retract-def-lemma g zero = 🐓🥚
retract-def-lemma g (suc n) = 🐓🥚

-- we're basically iterating over mini-colimit-diagrams .. always take the last vertex value 
extend-inductive-map : { A : Set } -> ( Nat -> A ) -> ( ( n m : Nat ) -> ( less-than n m ) -> A ) 
extend-inductive-map f zero (suc zero) (gt-zero .zero) = f zero
extend-inductive-map f zero (suc (suc m)) (gt-zero .(suc m)) = f ( suc m )
extend-inductive-map f (suc n) (suc m) (gt-suc .n .m pred) = f ( suc m )

{- TODO -- but I don't really care atm 
-- this really is an inclusion retraction relation, i.e. extending, then retracting should be strictly the identity on natural parameters 
retract-extend-inductive-map : { A : Set } 
                            -> ( f : Nat -> A ) 
                            -> ( ( n : Nat ) -> ( definition-equal ( f n ) ( ( retract-orderly-map ( extend-inductive-map f ) ) n ) ) )
retract-extend-inductive-map f zero = 🐓🥚 
retract-extend-inductive-map f (suc n) = {!   !}
    where g = extend-inductive-map f 
          h = retract-orderly-map g  -}

{- TODO -- auch noch nicht ganz
-- X set of subsets of an { 0, 1, .. n }  such that, intersections of subsets in X are always included in X too 
-- which means Xbar on { 0, 1, .. ( n - 1 ) } is a simplicial complex too, and in addition we need some simplices 
-- that are uniquely determined by a (possibly empty) left simplex in Xbar and the last vertex being n 
data is-simplicial-complex ( A : Set ) : Set where
     -}

-- wie generiere ich alle paare natuerlicher zahlen? Nat -> Nat .. und jetzt Listen verschiedener Paare natuerlicher 
-- zahlen xs list verschiedener paare  ++ zs liste von paaren die genau dann verschieden sind, wenn's ihre ersten elemente sind 

data Fin : Nat -> Set where 
    fzero : ( n : Nat ) -> Fin n
    succ : ( n : Nat ) -> Fin n -> Fin (suc n) 
{- 
data fin-less-than : { n : Nat } -> Fin n -> Fin n -> Set where 
    gt-zero : ( n : Nat ) -> ( prenonzero : Fin n ) -> ( fin-less-than ( fzero ( suc n ) ) ( succ n prenonzero ) )
    gt-succ : ( n : Nat ) -> ( a : Fin n ) -> ( b : Fin n ) -> ( fin-less-than { n = n } a b ) -> ( fin-less-than { n = ( suc n ) } ( succ n a ) ( succ n b ) ) -}

data Bool : Set where 
    true : Bool 
    false : Bool 

data dag : Nat -> Set where 
    empty-dag : dag zero 
    one-point-dag : dag ( suc zero ) 
    add-edges : { n : Nat } -> dag ( suc n ) -> ( Fin n -> Bool ) -> dag ( suc ( suc n ) ) 

dag-vertex-count : { n : Nat } -> dag n -> Nat 
dag-vertex-count { n = n } _ = n 

-- try def : transposing dag according to fin n stuerzen .. Fin * -> Fin * tau? 
-- dags are supposed to represent topological things, we will need a ( disjoint ) sum, suspension 
-- maybe product? preferably a mapping space that is itself a dag 

constant-false : ( A : Set ) -> ( A -> Bool ) 
constant-false A = \ _ -> false 

if_then_else_endif : { A : Set } -> Bool -> A -> A -> A 
if true then x else y endif = x
if false then x else y endif = y

lt-fun : ( n m : Nat ) -> Bool 
lt-fun zero zero = false
lt-fun zero (suc m) = true
lt-fun (suc n) zero = false
lt-fun (suc n) (suc m) = lt-fun n m

natural-equal : ( n m : Nat ) -> Bool 
natural-equal zero zero = true
natural-equal zero (suc m) = false
natural-equal (suc n) zero = false
natural-equal (suc n) (suc m) = natural-equal n m

open import Level using (Level;_⊔_)

record Sigma { k l : Level } ( B : Set k ) ( E : B -> Set l ) : Set ( k ⊔ l )  where 
    constructor _,_
    field 
        fst : B 
        snd : E fst 

infixr 50 _,_

data Pi { k l : Level } ( B : Set k ) ( E : B -> Set l ) : Set ( k ⊔ l ) where 
    dependent-function : ( ( x : B ) -> E x ) -> Pi B E 

-- Pi Nat Fin 