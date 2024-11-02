{-# OPTIONS --cubical-compatible --safe #-}

module StandardConstructions.AbstractNonsense.Product where 

--- then there was something
data Point : Set where 
    pt : Point 

data Product ( A B : Set ) : Set where 
    _,_ : A -> B -> Product A B 

infixr 4 _,_    

pr1 : { A B : Set } -> Product A B -> A 
pr1 ( a , _ ) = a 

pr2 : { A B : Set } -> Product A B -> B 
pr2 ( _ , b ) = b 

ass-product : { A B C : Set } -> ( Product ( Product A B ) C ) -> ( Product A ( Product B C ) ) 
ass-product ( ( a , b ) , c ) = ( a , b , c ) 

prod-point-l : { A : Set } -> ( Product Point A ) -> A 
prod-point-l ( pt , a ) = a 

prod-point-r : { A : Set } -> ( Product A Point ) -> A 
prod-point-r ( a , pt ) = a 

prod-point-l-t : { A : Set } -> A -> Product Point A  
prod-point-l-t a = ( pt , a ) 

prod-point-r-t : { A : Set } -> A -> Product A Point 
prod-point-r-t a = ( a , pt ) 

twist-prod : { A B : Set } -> Product A B -> Product B A 
twist-prod ( a , b ) = ( b , a ) 

twist-map : { A B Z : Set } -> ( Product A B -> Z ) -> ( Product B A -> Z ) 
twist-map f (b , a) = f (a , b)

induce-prod-maps : { A Y Z : Set } -> ( A -> Y ) -> ( A -> Z ) ->  ( A -> Product Y Z ) 
induce-prod-maps f g a = ( f a , g a ) 