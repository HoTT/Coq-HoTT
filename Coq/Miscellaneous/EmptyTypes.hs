
data NotReallyEmpty = Impossible NotReallyEmpty

test_once :: NotReallyEmpty -> Bool
test_once (Impossible _) = True

test_deeply :: NotReallyEmpty -> Bool
test_deeply (Impossible x) = test_deeply x

bottom :: NotReallyEmpty
bottom = error "Reached bottom!"

bottomless :: NotReallyEmpty
bottomless = Impossible bottomless

{-
*Main> test_once bottom
*** Exception: Reached bottom!
*Main> test_once (Impossible bottom)
True
*Main> test_deeply bottom
*** Exception: Reached bottom!
*Main> test_deeply bottomless
  ^C ^CInterrupted.
-}

data SlightlyEmptier = MoreImpossible !SlightlyEmptier

test_once' :: SlightlyEmptier -> Bool
test_once' (MoreImpossible _) = True

test_deeply' :: SlightlyEmptier -> Bool
test_deeply' (MoreImpossible x) = test_deeply' x

bottom' :: SlightlyEmptier
bottom' = error "Reached bottom!"

bottomless' :: SlightlyEmptier
bottomless' = MoreImpossible bottomless'

{-
*Main> test_depth' (bottom')
*** Exception: Reached bottom!
*Main> test_depth' (MoreImpossible bottom')
*** Exception: Reached bottom!
*Main> test_deeply' bottom'
*** Exception: Reached bottom!
*Main> test_deeply' bottomless'
  ^C ^CInterrupted.
-}