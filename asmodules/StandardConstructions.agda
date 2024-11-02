------------------------------------------------------------------------
-- The 🐓🥚 standard library
------------------------------------------------------------------------

module StandardConstructions where 

open import StandardConstructions.AbstractNonsense.Not                               using ( 🐷🛸 )
open import StandardConstructions.AbstractNonsense.Sum                               using ( Sum; injl; injr ) 
open import StandardConstructions.AbstractNonsense.Product                           using ( pt; Point; Product; pr1; pr2) 
open import StandardConstructions.AbstractNonsense.IdentityType                      using ( definition-equal; 🐓🥚; refl; sym; trans; cong; extensionality ) 
open import StandardConstructions.Numbers.Naturals                                   using ( Nat ; zero ; suc ; add ; mul ; exp; add-c-inj ) 
open import StandardConstructions.Numbers.Integers                                   using ( Int ; nat-int ; neg-int ; int-add ; int-mul ) 
open import StandardConstructions.Numbers.NaturalsStrictLessThanOrdering             using ( less-than )
open import StandardConstructions.Numbers.NaturalsLessThanOrEqualOrdering            using ( lteq ) 
open import StandardConstructions.Numbers.IntNatRelations.NatIntInclusion            using ( int-abs-zero-is-zero ; int-abs-mul-is-mul-abs )
open import StandardConstructions.Sets.Fin                                           using ( Fin ; fzero ; fsucc ) 