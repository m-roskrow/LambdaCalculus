import Data.Char
type Var = String

data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term

instance Show Term where
show = termTo

test :: Term
test = Lambda "a" (Lambda "x" (Apply (Apply (Lambda "y" (Variable "a")) (Variable "x")) (Variable "b")))

termTo :: Term -> String
termTo = f 0
  where
      f i (Variable x) = x
      f i (Lambda x m) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ". " ++ f 0 m 
      f i (Apply  n m) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m

numeral :: Int -> Term
numeral i = Lambda "f"(Lambda  "x"  (numeral'(i)))

numeral' :: Int -> Term
numeral' i
      | i == 0       = Variable "x"
      | i /= 0       = Apply (Variable "f") (numeral'(i-1))

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

variables :: [Var]
variables = "a": map nextVar variables

nextVar :: Var -> Var
nextVar ('z':[]) = "a1"
nextVar ('z':vs) = 'a':show ( read vs + 1)
nextVar (v:vs) = chr ( ord v + 1 ):vs

filterVariables :: [Var] -> [Var] -> [Var]
filterVariables vs [] = vs
filterVariables [] xs = []
filterVariables (v:vs) (x:xs)
      | v == x       =   filterVariables vs xs
      | otherwise    =   take 1 (filterVariables (v:vs) xs) ++ filterVariables vs (x:xs)

fresh :: [Var] -> Var
fresh [] =        head variables
fresh (v:vs) =    head (filterVariables variables (v:vs))

-- old "used" function which only worked with 1 char long vars, therefore has been replaced
{-
used :: Term -> [Var]
used t = used' (pretty t)

used' :: String -> [Var]
used' [] = []
used' (v:vs) 
    | isLetter v = usedFilter((v : usedCheck vs) : (used' vs))
    | otherwise  = used' vs

usedCheck :: String -> Var
usedCheck [] = []
usedCheck (v:vs)
    | isDigit v = v : usedCheck vs
    | otherwise = ""

usedFilter :: [Var] -> [Var]
usedFilter [] = []
usedFilter (v:vs) 
    | elem v vs = usedFilter vs
    | otherwise = merge [v] vs
-}

used :: Term -> [Var]
used t = usedFilter (used' t)

used' :: Term -> [Var]
used' (Apply n m) = used' n ++ used' m
used' (Lambda x n) = [x] ++ used' n
used' (Variable x) = [x]

usedFilter :: [Var] -> [Var]
usedFilter [] = []
usedFilter (v:vs) 
    | elem v vs = usedFilter vs
    | otherwise = merge [v] (usedFilter vs)

rename :: Var -> Var -> Term -> Term
rename x y (Variable z) =    if z == x    then (Variable y)    else (Variable z)
rename x y (Lambda z n) =    if z == x    then (Lambda y n)    else (Lambda z (rename x y n))
rename x y (Apply  n m) =    Apply (rename x y n)  (rename x y m)

substitute :: Var -> Term -> Term -> Term
substitute x n (Variable y)    = if y == x    then n            else (Variable y)
substitute x n (Lambda y m)    = if y == x    then (Lambda y m) else (Lambda z (substitute x n (rename y z m))) where z = fresh ([x] ++ used n ++ used m ++ [y])
substitute x n (Apply m1 m2)   = (Apply (substitute x n m1) (substitute x n m2))

beta :: Term -> [Term]
beta (Apply (Lambda x n) m)
   | (redexCheck m) && (redexCheck (Lambda x n)) = [substitute x m n] ++ [Apply (beta'(Lambda x n)) m] ++ [Apply (Lambda x n)  (beta' m)]
   | redexCheck (Lambda x n)                     = [substitute x m n] ++ [Apply (beta' (Lambda x n)) m]
   | redexCheck (m)                              = [substitute x m n] ++ [Apply (Lambda x n) (beta' m) ]
   | otherwise                                   = [substitute x m n]
beta (Variable x) = []
beta (Lambda x m)
   | redexCheck (m)                              = [Lambda x (beta' m)]
   | otherwise                                   = []
beta (Apply n m)
   | (redexCheck m) && (redexCheck n)            = [Apply (beta' n) (beta' m)]
   | (redexCheck m)                              = [Apply n (beta' m)]
   | (redexCheck n)                              = [Apply (beta' n) m]
   | otherwise                                   = []

beta' :: Term -> Term
beta' (Apply (Lambda x n) m) = substitute x m n
beta' (Variable x)           = (Variable x)
beta' (Lambda x m)           = (Lambda x (beta' m))
beta' (Apply n m)            = (Apply (beta' n) (beta' m))

redexCheck :: Term -> Bool
redexCheck (Apply (Lambda x n) m)     = True
redexCheck (Variable x)               = False
redexCheck (Lambda x m)               = redexCheck m
redexCheck (Apply n m)                = (redexCheck n || redexCheck m)

normalize :: Term -> IO ()
normalize t 
   | redexCheck t = (print t) >> normalize (head (beta t)) 
   | otherwise = print (t)
------------------------- 

a_beta :: Term -> [Term]
a_beta (Apply (Lambda x n) m)
   | (redexCheck m) && (redexCheck (Lambda x n)) = [substitute x m n] ++ [Apply (beta'(Lambda x n)) m] ++ [Apply (Lambda x n)  (beta' m)]
   | redexCheck (Lambda x n)                     = [substitute x m n] ++ [Apply (beta' (Lambda x n)) m]
   | redexCheck (m)                              = [substitute x m n] ++ [Apply (Lambda x n) (beta' m) ]
   | otherwise                                   = [substitute x m n]
a_beta (Variable x) = []
a_beta (Lambda x m)
   | redexCheck (m)                              = [Lambda x (beta' m)]
   | otherwise                                   = []
a_beta (Apply n m)
   | (redexCheck m) && (redexCheck n)            = [Apply (beta' n) (beta' m)]
   | (redexCheck m)                              = [Apply n (beta' m)]
   | (redexCheck n)                              = [Apply (beta' n) m]
   | otherwise                                   = []

a_normalize :: Term -> IO ()
a_normalize t 
   | redexCheck t = (print t) >> a_normalize (last (a_beta t)) 
   | otherwise = print (t)