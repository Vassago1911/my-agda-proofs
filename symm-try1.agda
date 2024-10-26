open import category-of-types-basics.definition-equal 
    using ( definition-equal; 🐓🥚; 🐷🛸;
            Point; pt; 
            cong; trans; eval-equal-maps; extensionality ) 
open import category-of-types-basics.category-sums 
    using ( Sum; injl; injr ) 
open import category-of-types-basics.map-rules 
    using ( id; circ )
open import category-of-types-objects.natural-rules 
    using ( Nat; zero; suc; 
            add; mul; exp; 
            suc-not-eq; suc-inj )
open import category-of-types-objects.fin-rules 
    using ( Fin; fzero; fsucc ) 
open import category-of-types-objects.ord-rules 
    using ( Ord ; ord-add ; ord-mul ; ord-exp ) 

-- test change 2