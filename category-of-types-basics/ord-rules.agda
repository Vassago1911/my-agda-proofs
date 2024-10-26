open import natural-rules using ( Nat ) 

data Ord : Set where
  zeroOrd : Ord
  sucOrd  : Ord → Ord
  limOrd  : (Nat → Ord) → Ord

ord-add : Ord -> Ord -> Ord 
ord-add zeroOrd y = y
ord-add (sucOrd x) y = ( sucOrd ( ord-add x y ) )
ord-add (limOrd x) y = limOrd ( fold-nat-map x y ) 
    where fold-nat-map : ( Nat -> Ord ) -> Ord -> ( Nat -> Ord ) 
          fold-nat-map f z n = ( ord-add z ( f n ) ) 

ord-mul : Ord -> Ord -> Ord 
ord-mul zeroOrd b = zeroOrd
ord-mul (sucOrd a) b = ( ord-add b ( ord-mul a b ) )
ord-mul (limOrd x) b = limOrd ( fold-nat-map x b )
    where fold-nat-map : ( Nat -> Ord ) -> Ord -> ( Nat -> Ord ) 
          fold-nat-map fn z n = ( ord-mul ( fn n ) z ) 

ord-exp : Ord -> Ord -> Ord 
ord-exp zeroOrd zeroOrd = sucOrd ( zeroOrd )
ord-exp zeroOrd (sucOrd b) = zeroOrd
ord-exp zeroOrd (limOrd x) = zeroOrd
ord-exp (sucOrd a) b = ( ord-add b ( ord-mul a b ) )
ord-exp (limOrd x) b = limOrd ( fold-nat-map x b ) 
    where fold-nat-map : ( Nat -> Ord ) -> Ord -> ( Nat -> Ord ) 
          fold-nat-map fn z n = ( ord-exp ( fn n ) z )
