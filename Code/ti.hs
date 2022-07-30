{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use bimap" #-}

data HType = HA String | HTup HType HType | HFunc HType HType deriving (Eq)

instance Show HType where
  show (HTup r1 r2) = "(" ++ show r1 ++ "," ++ show r2 ++ ")"
  show (HFunc r1 r2) = "(" ++ show r1 ++ "->" ++ show r2 ++ ")"
  show (HA t) = t

t1 :: HType
t1 = HTup (HA "Bool") (HFunc (HFunc (HA "a") (HA "Int")) (HA "Int"))

newtype Constraints = Constr [(HType, HType)]

instance Show Constraints where
  show (Constr cs) = show (map (\(x, y) -> show x ++ "=" ++ show y) cs) ++ " "

-- get all t_i inside a type
getHA :: HType -> [String]
getHA (HA t) = [t]
getHA (HTup s1 s2) = getHA s1 ++ getHA s2
getHA (HFunc s1 s2) = getHA s1 ++ getHA s2

-- check if constraints are in endform
endForm :: Constraints -> Bool
endForm (Constr cs)
  | all check cs = res
  | otherwise = error "doesn't type"
  where
    res = null [x | x <- lhs, x `elem` rhs]
    lhs = concatMap (getHA . fst) cs
    rhs = concatMap (getHA . snd) cs

-- check constraint
check :: (HType, HType) -> Bool
check (HA _, HA _) = True
check (HA x, t)
  | x == "Int" || x == "Bool" = False
  | otherwise = noRecursive x t
check (t, HA x)
  | x == "Int" || x == "Bool" = False
  | otherwise = noRecursive x t
check (_, _) = True

checkConstraints :: Constraints -> Bool
checkConstraints (Constr cs) = all check cs

-- for x=f(s0,...,sk), check that x!=si for all i
noRecursive :: String -> HType -> Bool
noRecursive s1 (HA s2) = s1 /= s2
noRecursive s1 t2 = s1 `notElem` getHA t2

-- swap elements if necessary
clean :: (HType, HType) -> (HType, HType)
-- t2=t1 for t1 = Bool/Int
clean (t1@(HA "Int"), t2@(HA _)) = (t2, t1)
clean (t1@(HA "Bool"), t2@(HA _)) = (t2, t1)
-- t2=t1 for t1 = x with x variable
clean (t1@(HTup _ _), t2@(HA _)) = (t2, t1)
clean (t1@(HFunc _ _), t2@(HA _)) = (t2, t1)
clean c = c

-- prepare
prepare :: Constraints -> Constraints
prepare (Constr cs)
  | all check cs = res
  | otherwise = error "doesn't type"
  where
    res = Constr $ map clean $ filter (uncurry (/=)) cs

-- transform constraint
transform :: (HType, HType) -> [(HType, HType)]
-- f(r1,r2)=f(s1, s2) to r1=s1, s2=s2
transform (HTup r1 r2, HTup s1 s2) = [(r1, s1), (r2, s2)]
transform (HFunc r1 r2, HFunc s1 s2) = [(r1, s1), (r2, s2)]
transform c@(HA x, _) = [c]
transform (_, _) = error "constraint doesn't unify"

-- transfom constraints
transformConstr :: Constraints -> Constraints
transformConstr (Constr cs) = Constr $ concatMap transform cs

-- substitute t in type
substitute :: (HType, HType) -> HType -> HType
substitute (HA x, f) t2@(HA s) = if x == s then f else t2
substitute sub (HTup t1 t2) = HTup (substitute sub t1) (substitute sub t2)
substitute sub (HFunc t1 t2) = HFunc (substitute sub t1) (substitute sub t2)
substitute _ _ = error "substitution not possible"

-- find constraint to substitute in others
subConstr :: String -> Constraints -> (HType, HType)
subConstr t0 (Constr cs) = aux cs
  where
    aux ((HA x, f) : cs) = if x /= t0 then (HA x, f) else aux cs
    aux (_ : cs) = aux cs
    aux [] = (HA "", HA "")

-- and substitute in constraints
substitution :: String -> Constraints -> Constraints
substitution t0 cons@(Constr cs) = Constr ncs
  where
    ncs = map (\(x, y) -> clean (aux x, aux y)) cs
    aux = substitute (subConstr t0 cons)

-- remove duplicates from constraints
removeDuplicates :: Constraints -> Constraints
removeDuplicates (Constr cs) = Constr $ aux cs
  where
    aux [] = []
    aux (x : xs)
      | x `elem` xs = aux xs
      | otherwise = x : aux xs

first :: Constraints -> Constraints
first = prepare

second :: Constraints -> Constraints
second = transformConstr . first

third :: String -> Constraints -> Constraints
third t0 = substitution t0 . second

iteration :: String -> Constraints -> Constraints
iteration t0 con
  | checkConstraints res = res
  | otherwise = error "doesn't unfiy"
  where
    res = prepare $ substitution t0 $ prepare $ transformConstr $ prepare con

unification :: String -> Constraints -> Constraints
unification t0 con
  | endForm con = removeDuplicates con
  | otherwise = unification t0 $ iteration t0 con

uct = unification "t0"

itt = iteration "t0"

cont :: Constraints
cont =
  Constr
    [ (HA "t0", HFunc (HA "t1") (HA "t2")),
      (HA "t2", HA "Bool"),
      (HA "t1", HTup (HFunc (HA "t3") (HA "Int")) (HA "t4")),
      (HA "t3", HTup (HA "t5") (HA "t6")),
      (HA "t5", HA "Int"),
      (HA "t6", HA "Bool")
    ]

cb :: Constraints
cb =
  Constr
    [ (HA "t0", HFunc (HA "t2") (HA "t3")),
      (HA "t2", HFunc (HA "t4") (HA "t3")),
      (HA "t4", HA "Bool"),
      (HA "t2", HFunc (HA "t5") (HA "Int")),
      (HA "t1", HA "t5"),
      (HA "t1", HA "Bool")
    ]

cc :: Constraints
cc =
  Constr
    [ (HA "t0", HFunc (HA "t1") (HA "t2")),
      (HA "t2", HFunc (HA "t3") (HA "t4")),
      (HA "t3", HFunc (HA "t5") (HA "Bool")),
      (HA "t1", HA "t5"),
      (HA "t1", HTup (HA "t4") (HA "t6")),
      (HA "t1", HTup (HA "t8") (HTup (HA "t7") (HA "t4")))
    ]

cd :: Constraints
cd =
  Constr
    [ (HA "t0", HA "Bool"),
      (HA "Int", HTup (HA "Int") (HA "t1"))
    ]

ce :: Constraints
ce =
  Constr
    [ (HA "t0", HA "Int"),
      (HFunc (HA "t2") (HA "t1"), HA "Bool"),
      (HA "t2", HA "Int")
    ]

data MHask
  = MVar String
  | MInt Int
  | MBool Bool
  | MLambda String MHask
  | MApp MHask MHask
  | MIszero MHask
  | MAdd MHask MHask
  | MMult MHask MHask
  | MIf MHask MHask MHask
  | MTup MHask MHask
  | MFst MHask
  | MSnd MHask
  deriving (Eq)

instance Show MHask where
  show (MVar v) = v
  show (MInt n) = show n
  show (MBool b) = show b
  show (MLambda x t) = "(\\" ++ x ++ " -> " ++ show t ++ ")"
  show (MApp t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"
  show (MIszero t) = "(isZero " ++ show t ++ ")"
  show (MAdd t1 t2) = "(" ++ show t1 ++ " + " ++ show t2 ++ ")"
  show (MMult t1 t2) = "(" ++ show t1 ++ " * " ++ show t2 ++ ")"
  show (MIf t0 t1 t2) = "(if " ++ show t0 ++ " then " ++ show t1 ++ " else " ++ show t2 ++ ")"
  show (MTup t1 t2) = "(" ++ show t1 ++ "," ++ show t2 ++ ")"
  show (MFst t) = "(fst " ++ show t ++ ")"
  show (MSnd t) = "(snd  " ++ show t ++ ")"

m1 :: MHask
m1 = MLambda "x" (MTup (MApp (MApp (MVar "x") (MInt 1)) (MBool True)) (MApp (MVar "x") (MInt 0)))


data Rule = RVar | RAbs | RApp | RIszero | RInt | RTrue | RFalse | RBinOp | RIf | RTup | RFst | RSnd 
data DerTree = Leaf | UNode [(MHask, HType)] (MHask, HType) Rule

-- getType :: MHask -> HType