open import category-sums using ( Sum; injl; injr ) 
--- then there was something, the (univalence axiom foreshadowing, in principle "a") one point type 
data Point : Set where 
    pt : Point 

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