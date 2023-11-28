-- id : forall a. a -> a
-- twice : forall a. (a -> a) -> a -> a

let inc n = n + 1;

-- not : Bool -> Bool
let not b = if b then false else true;

let poly x y = if twice not (id false)
                 then id (twice inc x)
                 else twice inc (id y)
               ;
