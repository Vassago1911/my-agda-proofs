module StandardConstructions.Fin where 

open import StandardConstructions.Naturals using ( Nat ; suc ) 

data Fin : Nat -> Set where 
    fzero : { k : Nat } -> Fin ( suc k ) 
    fsucc : { k : Nat } -> Fin k -> Fin ( suc k ) 
