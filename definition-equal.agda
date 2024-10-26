--- at first there was nothing
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

not : Set -> Set 
not A = ( A -> 🐷🛸 )

map-not : { A B : Set } -> ( f : A -> B ) -> ( not B -> not A ) 
map-not f notb a = notb ( f a )

data definition-equal {a} { A : Set a } : A -> A -> Set a where 
    🐓🥚 : { x : A } -> definition-equal x x 

cong : { A B : Set } { x y : A } -> ( f : A -> B ) -> ( definition-equal x y ) -> ( definition-equal ( f x ) ( f y ) ) 
cong f 🐓🥚 = 🐓🥚 

refl : { A : Set } { x : A } -> ( definition-equal x x ) 
refl = 🐓🥚

sym : { A : Set } { x y : A } -> ( definition-equal x y ) -> ( definition-equal y x ) 
sym 🐓🥚 = 🐓🥚

trans : { A : Set } { x y z : A } -> ( definition-equal x y ) -> ( definition-equal y z ) -> ( definition-equal x z ) 
trans 🐓🥚 🐓🥚 = 🐓🥚

eval-equal-maps : { A B : Set } -> { f : A -> B } -> { g : A -> B } -> ( definition-equal f g ) -> ( ( x : A ) -> ( definition-equal ( f x ) ( g x ) ) ) 
eval-equal-maps 🐓🥚 x = 🐓🥚 

{-# BUILTIN EQUALITY definition-equal #-} 

-- it is weaker than univalence or similar weaker axioms to assume extensionality, so we will do so 
postulate
  extensionality : {A B : Set} {f g : A -> B}
    -> ((x : A) -> ( definition-equal ( f x ) ( g x ) ))
      -----------------------
    -> ( definition-equal f g )

