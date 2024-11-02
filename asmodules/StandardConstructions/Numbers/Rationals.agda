module StandardConstructions.Numbers.Rationals where 

open import StandardConstructions.Numbers.Naturals using ( Nat; zero; suc ) 
open import StandardConstructions.Numbers.Naturals-GCD using ( GCD ) 

data Rationals : Set where 
    pfraction : ( n m : Nat ) -> { GCD n m (suc zero) } -> Rationals 
    nfraction : ( n m : Nat ) -> { GCD n m (suc zero) } -> Rationals
    zero : Rationals

-- addition is easy because we restricted to gcd suc zero 
-- multiplication should be even simpler 
-- less-than will be .. annoying?

rat-minus : Rationals -> Rationals 
rat-minus (pfraction n m {pred} ) = (nfraction n m {pred} )  
rat-minus (nfraction n m {pred} ) = (pfraction n m {pred} )  
rat-minus zero = zero 

rat-add : Rationals -> Rationals -> Rationals 
rat-add q zero = q
rat-add zero q = q
rat-add (pfraction n m {prednm}) (pfraction p q {predpq}) = {!   !}
rat-add (pfraction n m {prednm}) (nfraction p q {predpq}) = {!   !}
rat-add (nfraction n m {prednm}) (pfraction p q {predpq}) = {!   !}
rat-add (nfraction n m {prednm}) (nfraction p q {predpq}) = {!   !}

data Boolean : Set where 
    true : Boolean 
    false : Boolean

data RationalSubset : Set where 
    rational-subset : ( Rationals -> Boolean ) -> RationalSubset

    
{- needs less than 
data RationalSubInterval : Set where 
    rational-subinterval : ( P : RationalSubset ) 
                    -> ( ( x y  -}