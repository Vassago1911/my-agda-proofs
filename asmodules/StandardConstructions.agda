------------------------------------------------------------------------
-- The 🐓🥚 standard library
------------------------------------------------------------------------

module StandardConstructions where 

open import StandardConstructions.Sum                               using ( Sum; injl; injr ) 
open import StandardConstructions.Product                           using ( pt; Point; Product; pr1; pr2) 
open import StandardConstructions.IdentityType                      using ( definition-equal; 🐓🥚; refl; sym; trans; cong; extensionality ) 
open import StandardConstructions.Naturals                          using ( Nat ; zero ; suc ; add ; mul ; exp ) 
open import StandardConstructions.NaturalsStrictLessThanOrdering    using ( less-than )
open import StandardConstructions.NaturalsLessThanOrEqualOrdering   using ( lteq ) 
open import StandardConstructions.Not                               using ( 🐷🛸 )
open import StandardConstructions.Fin                               using ( Fin ; fzero ; fsucc ) 