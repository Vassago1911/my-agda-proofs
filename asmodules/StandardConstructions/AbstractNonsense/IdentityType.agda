{-# OPTIONS --cubical-compatible #-}

module StandardConstructions.AbstractNonsense.IdentityType where 

open import StandardConstructions.AbstractNonsense.IgnorableStandard.Level 

data definition-equal { a : Level } { A : Set a } : A -> A -> Set a where 
    🐓🥚 : { x : A } -> definition-equal x x 

cong : { A B : Set } { x y : A } -> ( f : A -> B ) -> ( definition-equal x y ) -> ( definition-equal ( f x ) ( f y ) ) 
cong f 🐓🥚 = 🐓🥚 

typey-cong : { a b : Level } { A : Set a } { B : A -> Set b } 
      -> ( x y : A ) 
      -> ( definition-equal x y ) 
      -> ( definition-equal (B x) (B y) )
typey-cong x y 🐓🥚 = 🐓🥚

cong2 : { A B C : Set } { x y : A } { a b : B } -> ( f : A -> B -> C ) 
    -> ( definition-equal x y ) -> ( definition-equal a b ) 
    -> ( definition-equal ( f x a ) ( f y b ) ) 
cong2 f 🐓🥚 🐓🥚 = 🐓🥚    

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