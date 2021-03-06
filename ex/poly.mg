infixl 8 +;

-- id : forall a. a -> a
-- double : forall a. (a -> a) -> a -> a
let id = \a => a
in let double = \f => \a => f (f a)
   in let inc = \n => n + 1
      in let not = \b => if b then false else true
         in if double not (id false)
            then id (double inc 3)
            else double inc (id 7)
