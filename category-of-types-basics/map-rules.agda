id : { A : Set } -> ( A -> A ) 
id = \ x -> x 

circ : { A B C : Set } -> ( B -> C ) -> ( A -> B ) -> ( A -> C ) 
circ g f = \ a -> g ( f a ) 