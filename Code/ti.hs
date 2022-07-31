{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use bimap" #-}

data HType = HA String | HTup HType HType | HFunc HType HType deriving (Eq)

instance Show HType where
  show (HTup r1 r2) = "(" ++ show r1 ++ "," ++ show r2 ++ ")"
  show (HFunc r1 r2) = "(" ++ show r1 ++ "->" ++ show r2 ++ ")"
  show (HA t) = t

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

-- check if constraint is unifiable
check :: (HType, HType) -> Bool
check (HA _, HA _) = True
check (HA x, t)
  | x == "Int" || x == "Bool" = False
  | otherwise = noRecursive x t
check (t, HA x)
  | x == "Int" || x == "Bool" = False
  | otherwise = noRecursive x t
check (_, _) = True

-- for x=f(s0,...,sk), check that x!=si for all i
noRecursive :: String -> HType -> Bool
noRecursive s1 (HA s2) = s1 /= s2
noRecursive s1 t2 = s1 `notElem` getHA t2

checkConstraints :: Constraints -> Bool
checkConstraints (Constr cs) = all check cs

-- swap elements if necessary
clean :: (HType, HType) -> (HType, HType)
-- t2=t1 for t1 = Bool/Int
clean (t1@(HA "Int"), t2@(HA _)) = (t2, t1)
clean (t1@(HA "Bool"), t2@(HA _)) = (t2, t1)
-- t2=t1 for t1 = x with x variable
clean (t1@(HTup _ _), t2@(HA _)) = (t2, t1)
clean (t1@(HFunc _ _), t2@(HA _)) = (t2, t1)
clean c = c

-- prepare: check all constraints, remove trivial
prepare :: Constraints -> Constraints
prepare (Constr cs)
  | all check cs = res
  | otherwise = error "doesn't type"
  where
    res = Constr $ map clean $ filter (uncurry (/=)) cs

-- transform constraint: f(r1,r2)=f(s1, s2) to r1=s1, s2=s2
transform :: (HType, HType) -> [(HType, HType)]
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

iteration :: Constraints -> Constraints
iteration con
  | checkConstraints res = res
  | otherwise = error "doesn't unfiy"
  where
    res = prepare $ substitution "t0" $ prepare $ transformConstr $ prepare con

unification ::  Constraints -> Constraints
unification con
  | endForm con = removeDuplicates con
  | otherwise = unification $ iteration con


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
  show (MLambda x e) = "(\\" ++ x ++ " -> " ++ show e ++ ")"
  show (MApp e1 e2) = "(" ++ show e1 ++ " " ++ show e2 ++ ")"
  show (MIszero e) = "(isZero " ++ show e ++ ")"
  show (MAdd e1 e2) = "(" ++ show e1 ++ " + " ++ show e2 ++ ")"
  show (MMult e1 e2) = "(" ++ show e1 ++ " * " ++ show e2 ++ ")"
  show (MIf e0 e1 e2) = "(if " ++ show e0 ++ " then " ++ show e1 ++ " else " ++ show e2 ++ ")"
  show (MTup e1 e2) = "(" ++ show e1 ++ "," ++ show e2 ++ ")"
  show (MFst e) = "(fst " ++ show e ++ ")"
  show (MSnd e) = "(snd  " ++ show e ++ ")"

data Entails = Ent [(MHask, HType)] MHask HType

instance Show Entails where
  show (Ent cs e t) = concatMap (\(e, t) -> show e ++ ":" ++ show t ++ " ") cs ++ "|- " ++ show e ++ "::" ++ show t

findAssum :: [(MHask, HType)] -> MHask -> HType
findAssum [] _ = error "no assumptions yet/no more assumptions"
findAssum ((m, t) : as) mk
  | m == mk = t
  | otherwise = findAssum as mk

go :: Entails -> Constraints -> Int -> ([Entails], Constraints, Int)
-- Var
go (Ent gamma e@(MVar x) t) constr@(Constr cs) counter =
  ([], Constr ((findAssum gamma e, t) : cs), counter)
-- Abs
go (Ent gamma (MLambda x e) (HFunc t1 t2)) constr@(Constr cs) counter =
  ([Ent ((MVar x, t1) : gamma) e t2], constr, counter) -- no new constraint
go (Ent gamma (MLambda x e) t) constr@(Constr cs) counter =
  ([Ent ((MVar x, tnext) : gamma) e tnextp1], Constr ((t, HFunc tnext tnextp1) : cs), counter + 2) -- new constraint
  where
    tnext = HA ("t" ++ show counter)
    tnextp1 = HA ("t" ++ show (counter + 1))
-- App
go (Ent gamma (MApp e1 e2) t) constr@(Constr cs) counter =
  ([Ent gamma e1 (HFunc tnext t), Ent gamma e2 tnext], constr, counter + 1)
  where
    tnext = HA ("t" ++ show counter)
-- iszero
go (Ent gamma (MIszero e) t) constr@(Constr cs) counter =
  ([Ent gamma e (HA "Int")], Constr ((t, HA "Bool") : cs), counter)
-- int
go (Ent gamma (MInt n) t) constr@(Constr cs) counter =
  ([], Constr ((t, HA "Int") : cs), counter)
-- true/false
go (Ent gamma (MBool b) t) constr@(Constr cs) counter =
  ([], Constr ((t, HA "Bool") : cs), counter)
-- BinOp
go (Ent gamma (MAdd e1 e2) t) constr@(Constr cs) counter =
  ([Ent gamma e1 (HA "Int"), Ent gamma e2 (HA "Int")], Constr ((t, HA "Int") : cs), counter)
go (Ent gamma (MMult e1 e2) t) constr@(Constr cs) counter =
  ([Ent gamma e1 (HA "Int"), Ent gamma e2 (HA "Int")], Constr ((t, HA "Int") : cs), counter)
-- If
go (Ent gamma (MIf b e1 e2) t) constr@(Constr cs) counter =
  ([Ent gamma b (HA "Bool"), Ent gamma e1 t, Ent gamma e2 t], constr, counter)
-- Tuple
go (Ent gamma (MTup e1 e2) (HTup t1 t2)) constr@(Constr cs) counter =
  ([Ent gamma e1 t1, Ent gamma e2 t2], constr, counter) -- no new constraint
go (Ent gamma (MTup e1 e2) t) constr@(Constr cs) counter =
  ([Ent gamma e1 tnext, Ent gamma e2 tnextp1], Constr ((t, HTup tnext tnextp1) : cs), counter + 2) -- new constraint
  where
    tnext = HA ("t" ++ show counter)
    tnextp1 = HA ("t" ++ show (counter + 1))
-- fst
go (Ent gamma (MFst e) t) constr@(Constr cs) counter =
  ([Ent gamma e (HTup t tnext)], constr, counter + 1)
  where
    tnext = HA ("t" ++ show counter)
-- snd
go (Ent gamma (MSnd e) t) constr@(Constr cs) counter =
  ([Ent gamma e (HTup tnext t)], constr, counter + 1)
  where
    tnext = HA ("t" ++ show counter)

root ::  MHask -> Entails
root m = Ent [] m (HA "t0")

iter :: ([Entails], Constraints, Int ) -> ([Entails], Constraints, Int )
iter r@([], constr, counter) =  r
iter (ent: es, constr, count) = (newents ++ es, newconstr, newcount)
  where
    (newents, newconstr, newcount) = go ent constr count

getConstraints :: MHask -> Constraints
getConstraints e = aux [root e] (Constr []) 1

aux :: [Entails] -> Constraints -> Int -> Constraints
aux [] constr _ = constr
aux (ent : es) constr count = aux (newents ++ es) newconstr newcount
  where
    (newents, newconstr, newcount) = go ent constr count

findConstraint :: Constraints -> HType ->  HType
findConstraint (Constr []) t = t
findConstraint (Constr ((tk, tv):cs)) t
  | tk == t = tv
  | otherwise = findConstraint (Constr cs) t

getType :: MHask -> HType
getType m = findConstraint sol (HA "t0")
  where
    sol = unification (getConstraints m)

-- Examples to test

e1 :: MHask
e1 = MLambda "x" (MIszero (MVar "x"))

e2 :: MHask
e2 = MLambda "x" (MTup (MApp (MApp (MVar "x") (MInt 1)) (MBool True)) (MApp (MVar "x") (MInt 0)))

e3 :: MHask
e3 = MApp (MLambda "x" (MLambda "y" (MApp (MVar "y") (MIszero (MApp (MVar "y") (MVar "x")))))) (MBool True)

e4 :: MHask
e4 = MLambda "x" (MLambda "y" ( MIf  (MApp (MVar "y") (MVar "x")) (MFst (MVar "x")) (MSnd (MSnd (MVar "x"))) ))

e5 :: MHask
e5 = MIszero (MFst (MAdd (MInt 3) (MInt 5)))

e6 :: MHask
e6 = MApp (MLambda "x" (MInt 0)) (MApp (MBool True) (MInt 5))

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

ent2 :: Entails
ent2 = Ent [(MVar "x", HA "t1")] (MVar "x") (HA "t2")

ent3 :: Entails
ent3 = Ent [] (MApp (MVar "x") (MVar "y")) (HA "t0")

ent4 :: Entails
ent4 = Ent [] (MIszero (MVar "x")) (HA "t0")

ent5 :: Entails
ent5 = Ent [] (MBool True) (HA "t0")

ent6 :: Entails
ent6 = Ent [] (MAdd (MVar "x") (MVar "y")) (HA "t0")

ent7 :: Entails
ent7 = Ent [] (MIf (MVar "b") (MVar "x") (MVar "y")) (HA "t0")

ent8 :: Entails
ent8 = Ent [] (MTup (MVar "x") (MVar "y")) (HTup (HA "t0") (HA "t1"))

ent9 :: Entails
ent9 = Ent [] (MSnd (MVar "x")) (HA "t0")

-- Code dump

-- applyRule :: Entails -> [Entails]
-- -- Var
-- applyRule (Ent gamma (MVar x) _) = []
-- -- Abs
-- applyRule (Ent gamma (MLambda x e) (HFunc t1 t2)) = [Ent ((MVar x, t1) : gamma) e t2]
-- -- App
-- applyRule (Ent gamma (MApp e1 e2) t1) = [Ent gamma e1 (HFunc (HA "a") t1), Ent gamma e2 (HA "a")]
-- -- iszero
-- applyRule (Ent gamma (MIszero e) (HA "Bool")) = [Ent gamma e (HA "Int")]
-- -- Int
-- applyRule (Ent gamma (MInt n) (HA "Int")) = []
-- -- True/False
-- applyRule (Ent gamma (MBool b) (HA "Bool")) = []
-- -- BinOp
-- applyRule (Ent gamma (MAdd e1 e2) (HA "Int")) = [Ent gamma e1 (HA "Int"), Ent gamma e2 (HA "Int")]
-- applyRule (Ent gamma (MMult e1 e2) (HA "Int")) = [Ent gamma e1 (HA "Int"), Ent gamma e2 (HA "Int")]
-- -- if
-- applyRule (Ent gamma (MIf b e1 e2) t) = [Ent gamma b (HA "Bool"), Ent gamma e1 t, Ent gamma e2 t]
-- -- Tuple
-- applyRule (Ent gamma (MTup e1 e2) (HTup t1 t2)) = [Ent gamma e1 t1, Ent gamma e2 t2]
-- -- fst
-- applyRule (Ent gamma (MFst e) t) = [Ent gamma e (HTup t (HA "b"))]
-- -- snd
-- applyRule (Ent gamma (MSnd e) t) = [Ent gamma e (HTup (HA "a") t)]
-- applyRule ent = error (show ent ++ " type is not correct")

-- -- sometimes verifies if a type is correct -> alpha conversion not implemented
-- verify :: Entails -> [Entails]
-- verify ent = aux $ applyRule ent
--   where
--     aux [] = []
--     aux xs = aux $ concatMap applyRule xs

-- data DerTree = Leaf | UNode Rule Entails DerTree | BNode Rule Entails DerTree DerTree | TNode Rule Entails DerTree DerTree DerTree

-- instance Show DerTree where
--   show Leaf = "_"
--   show (UNode r ent st) = "(" ++ show ent ++ " [" ++ show r ++ "] " ++ show st ++ ")"
--   show (BNode r ent st1 st2) = "(" ++ show ent ++ " [" ++ show r ++ "] " ++ show st1 ++ " | " ++ show st2 ++ ")"
--   show (TNode r ent st1 st2 st3) = "(" ++show ent ++ " [" ++ show r ++ "] " ++ show st1 ++ " | " ++ show st2 ++ " | " ++ show st3 ++ ")"

-- vard :: DerTree
-- vard = UNode RVar ent Leaf

-- absd :: DerTree
-- absd = BNode RAbs ent vard vard

-- getType :: MHask -> HType

-- data Rule = RVar | RAbs | RApp | RIszero | RInt | RTrue | RFalse | RPlus | RTimes | RIf | RTup | RFst | RSnd

-- instance Show Rule where
--   show RVar = "Var"
--   show RAbs = "Abs"
--   show RApp = "App"
--   show RIszero = "iszero"
--   show RInt = "Int"
--   show RTrue = "True"
--   show RFalse = "False"
--   show RPlus = "+"
--   show RTimes = "*"
--   show RIf = "if"
--   show RTup = "Tuple"
--   show RFst = "fst"
--   show RSnd = "snd"