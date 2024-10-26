open import definition-equal using ( 🐷🛸; 🐓🥚; definition-equal ) 

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