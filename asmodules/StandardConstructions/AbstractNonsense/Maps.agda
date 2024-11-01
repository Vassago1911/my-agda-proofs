module StandardConstructions.AbstractNonsense.Maps where 

id : { A : Set } -> ( A -> A ) 
id a = a 

circ : { A B C : Set } -> ( B -> C ) -> ( A -> B ) -> ( A -> C ) 
circ g f a = g ( f a ) 