import Data.Char
import System.IO

slice xs from to = take (to - from + 1) (drop from xs)
removeUntil :: Eq a => a -> [a] -> [a]
removeUntil o [] = []
removeUntil o (x:xs) = if o == x then xs else removeUntil o xs

data Type = IntT | FloatT | BoolT | StringT
  deriving Eq
instance Show Type where
  show IntT = "Integer"
  show BoolT = "Boolean"
  show FloatT = "Float"
  show StringT = "String"

type TypeConstr = (String, Type)
data Value = IntVal Integer | FloatVal Float | BoolVal Bool | StringVal String | ErrVal String
  deriving Show
data Expr = IEx IExpr | BEx BExpr | FEx FExpr | SEx SExpr
  deriving Show
type VarName = String
type Error = String

type Params = (String, Type)
type Func = (String, [Params], [Instr])
fname :: Func -> String
fname (name, _, _) = name
fparams :: Func -> [Params]
fparams (_, params, _) = params
funcdef :: Func -> [Instr]
funcdef (_, _, def) = def

data IExpr = IVar VarName | IConst Integer
           | Add IExpr IExpr | Sub IExpr IExpr
           | Mul IExpr IExpr | Div IExpr IExpr
           | Pow IExpr IExpr | Mod IExpr IExpr
           | Len SExpr | Floor FExpr
           | IApp String [Expr]
           deriving Show

data FExpr = FVar VarName | FConst Float
           | FAdd FExpr FExpr | FSub FExpr FExpr
           | FMul FExpr FExpr | FDiv FExpr FExpr
           | FApp String [Expr] | ItoFloat IExpr
           deriving Show

data BExpr = BVar VarName | TT | FF
           | And BExpr BExpr | Or BExpr BExpr | Not BExpr
           | IEql IExpr IExpr
           | ILt  IExpr IExpr
           | ILte IExpr IExpr
           | FEql FExpr FExpr
           | FLt  FExpr FExpr
           | FLte FExpr FExpr
           | SEql SExpr SExpr
           | BApp String [Expr]
           deriving Show

data SExpr = SVar VarName | SConst String | Cat SExpr SExpr
           | Idx SExpr IExpr | Slc SExpr IExpr IExpr
           | ItoString IExpr
           | FtoString FExpr
           | BtoString BExpr
           | SApp String [Expr]
           deriving Show

type Env = [(VarName, Value)]

findnew :: Env -> String
findnew env = show $ (maxn 0 env) + 1

maxn :: Integer -> Env -> Integer
maxn n [] = n
maxn n ((x,_):xs) | all isDigit x = if (read x) > n
                                    then maxn (read x) xs
                                    else maxn n xs
                | otherwise = maxn n xs

update :: (VarName, Value) -> Env -> Env
update (x,v) env | x == "" = (findnew env, v):env
update (x,v) [] = [(x, v)]
update (x,v) ((name,val):env) = if x == name then (x,v):env
                                           else (name,val):(update (x,v) env)

mapEval :: (a -> b -> c) -> Either a Error -> Either b Error -> Either c Error
mapEval f (Right err) _ = Right err
mapEval f _ (Right err) = Right err
mapEval f a b = case a of Left x -> case b of Left y -> Left $ f x y

lookupFunc :: [Func] -> String -> Maybe Func
lookupFunc [] s = Nothing
lookupFunc (f:fs) s = if fname f == s then Just f else lookupFunc fs s

prepareFEnv :: [Func] -> String -> Env -> [Expr] -> Either Env Error
prepareFEnv fs fn env vs = case lookupFunc fs fn of
                              Nothing -> Right $ "Call on undefined function " ++ fn
                              Just f -> case prepareFEnv2 fs (fname f) (fparams f) env vs of
                                Right err -> Right err
                                Left env -> Left env

prepareFEnv2 :: [Func] -> String -> [Params] -> Env -> [Expr] -> Either Env Error
prepareFEnv2 fs fn [] env [] = Left []
prepareFEnv2 fs fn x env [] = Right $ "Invalid number of arguments given to function " ++ fn
prepareFEnv2 fs fn [] env x = Right $ "Invalid number of arguments given to function " ++ fn
prepareFEnv2 fs fn ((v, t):ps) env ((IEx i):es) = case t of
                                                IntT -> case prepareFEnv2 fs fn ps env es of
                                                          Right error -> Right error
                                                          Left env2 -> case (evali fs env i) of
                                                            Left ii -> Left $ (v, IntVal ii):env2
                                                            Right err -> Right err
                                                otherwise -> Right $ "Integer supplied to " ++ (show t) ++ " argument of function " ++ fn
prepareFEnv2 fs fn ((v, t):ps) env ((FEx i):es) = case t of
                                                FloatT -> case prepareFEnv2 fs fn ps env es of
                                                          Right error -> Right error
                                                          Left env2 -> case (evalf fs env i) of
                                                            Left ii -> Left $ (v, FloatVal ii):env2
                                                            Right err -> Right err
                                                otherwise -> Right $ "Float supplied to " ++ (show t) ++ " argument of function " ++ fn
prepareFEnv2 fs fn ((v, t):ps) env ((BEx i):es) = case t of
                                                BoolT -> case prepareFEnv2 fs fn ps env es of
                                                          Right error -> Right error
                                                          Left env2 -> case (evalb fs env i) of
                                                            Left ii -> Left $ (v, BoolVal ii):env2
                                                            Right err -> Right err
                                                otherwise -> Right $ "Boolean supplied to " ++ (show t) ++ " argument of function " ++ fn
prepareFEnv2 fs fn ((v, t):ps) env ((SEx i):es) = case t of
                                                StringT -> case prepareFEnv2 fs fn ps env es of
                                                          Right error -> Right error
                                                          Left env2 -> case (evals fs env i) of
                                                            Left ii -> Left $ (v, StringVal ii):env2
                                                            Right err -> Right err
                                                otherwise -> Right $ "String supplied to " ++ (show t) ++ " argument of function " ++ fn

evalFunc :: [Func] -> String -> [Expr] -> Env -> Either Value Error
evalFunc fs fn es env = case lookupFunc fs fn of
                          Nothing -> Right $ "Function " ++ fn ++ " not found."
                          Just f -> case (prepareFEnv fs fn env es) of
                                      Left fenv -> let (res, fs2) = execList fs (funcdef f) fenv in
                                                      case lookup "1" res of
                                                          Nothing -> Right $ "Function " ++ fn ++ " did not return a value"
                                                          Just v -> Left v
                                      Right err -> Right err



evali :: [Func] -> Env -> IExpr -> Either Integer Error
evali fs env (IVar v) = case lookup v env of
                        Nothing -> Right $ "Error: Variable " ++ v ++ " not found."
                        Just (IntVal n) -> Left n
                        Just other -> Right $ "TypeError: Variable " ++ v ++ " used as integer."
evali fs env (IConst n) = Left n
evali fs env (Add i1 i2) = mapEval (+) (evali fs env i1) (evali fs env i2)
evali fs env (Sub i1 i2) = mapEval (-) (evali fs env i1) (evali fs env i2)
evali fs env (Mul i1 i2) = mapEval (*) (evali fs env i1) (evali fs env i2)
evali fs env (Div i1 i2) = mapEval (div) (evali fs env i1) (evali fs env i2)
evali fs env (Pow i1 i2) = mapEval (^) (evali fs env i1) (evali fs env i2)
evali fs env (Mod i1 i2) = mapEval (mod) (evali fs env i1) (evali fs env i2)
evali fs env (Len s1) = case evals fs env s1 of
                          Right err -> Right err
                          Left str -> Left $ toInteger $ length str
evali fs env (Floor f) = case evalf fs env f of
                          Right err -> Right err
                          Left ft -> Left $ floor ft
evali fs env (IApp fn es) = case evalFunc fs fn es env of
                              Right err -> Right err
                              Left val -> case val of
                                            IntVal n -> Left n
                                            otherwise -> Right $ "Function " ++ fn ++ " returned invalid type"

evalf :: [Func] -> Env -> FExpr -> Either Float Error
evalf fs env (FVar v) = case lookup v env of
                        Nothing -> Right $ "Error: Variable " ++ v ++ " not found."
                        Just (FloatVal f) -> Left f
                        Just other -> Right $ "TypeError: Variable " ++ v ++ " used as float."
evalf fs env (FConst f) = Left f
evalf fs env (FAdd f1 f2) = mapEval (+) (evalf fs env f1) (evalf fs env f2)
evalf fs env (FSub f1 f2) = mapEval (-) (evalf fs env f1) (evalf fs env f2)
evalf fs env (FMul f1 f2) = mapEval (*) (evalf fs env f1) (evalf fs env f2)
evalf fs env (FDiv f1 f2) = mapEval (/) (evalf fs env f1) (evalf fs env f2)
evalf fs env (ItoFloat i) = case evali fs env i of
                              Right err -> Right err
                              Left n -> Left $ fromIntegral n
evalf fs env (FApp fn es) = case evalFunc fs fn es env of
                              Right err -> Right err
                              Left val -> case val of
                                            FloatVal n -> Left n
                                            otherwise -> Right $ "Function " ++ fn ++ " returned invalid type"

evals :: [Func] -> Env -> SExpr -> Either String Error
evals fs env (SVar v) = case lookup v env of
                        Nothing -> Right $ "Error: Variable " ++ v ++ " not found."
                        Just (StringVal str) -> Left str
                        Just other -> Right $ "TypeError: Variable " ++ v ++ " used as string."
evals fs env (SConst s) = Left s
evals fs env (Cat s1 s2) = mapEval (++) (evals fs env s1) (evals fs env s2)
evals fs env (Idx s1 i1) = case evals fs env s1 of
                          Right err -> Right err
                          Left str ->
                            case evali fs env i1 of
                              Right err -> Right err
                              Left n -> if n < 0 || n >= (toInteger $ length str)
                                          then Right $ "Index " ++ (show n) ++ " out of bounds for string " ++ str
                                          else Left $ [str !! (fromIntegral n)]
evals fs env (Slc s1 i1 i2) = case evals fs env s1 of
                              Right err -> Right err
                              Left str ->
                                case evali fs env i1 of
                                  Right err -> Right err
                                  Left n1 ->
                                    case evali fs env i2 of
                                      Right err -> Right err
                                      Left n2 -> Left $ slice str (fromIntegral n1) (fromIntegral n2)
evals fs env (ItoString i) = case evali fs env i of
                              Right err -> Right err
                              Left n -> Left $ show n
evals fs env (FtoString f) = case evalf fs env f of
                              Right err -> Right err
                              Left n -> Left $ show n
evals fs env (BtoString b) = case evalb fs env b of
                              Right err -> Right err
                              Left bl -> Left $ show bl
evals fs env (SApp fn es) = case evalFunc fs fn es env of
                              Right err -> Right err
                              Left val -> case val of
                                            StringVal n -> Left n
                                            otherwise -> Right $ "Function " ++ fn ++ " returned invalid type"

evalb :: [Func] -> Env -> BExpr -> Either Bool Error
evalb fs env (BVar v) = case lookup v env of
                        Nothing -> Right $ "Error: Variable " ++ v ++ " not found."
                        Just (BoolVal b) -> Left b
                        Just other -> Right $ "TypeError: Variable " ++ v ++ " used as boolean."
evalb fs env TT = Left True
evalb fs env FF = Left False
evalb fs env (And b1 b2) = mapEval (&&) (evalb fs env b1) (evalb fs env b2)
evalb fs env (Or b1 b2) = mapEval (||) (evalb fs env b1) (evalb fs env b2)
evalb fs env (Not b) = case evalb fs env b of
                      Right err -> Right err
                      Left bool -> Left $ not bool
evalb fs env (IEql i1 i2) = mapEval (==) (evali fs env i1) (evali fs env i2)
evalb fs env (ILt i1 i2) = mapEval (<) (evali fs env i1) (evali fs env i2)
evalb fs env (ILte i1 i2) = mapEval (<=) (evali fs env i1) (evali fs env i2)
evalb fs env (FEql f1 f2) = mapEval (==) (evalf fs env f1) (evalf fs env f2)
evalb fs env (FLt f1 f2) = mapEval (<) (evalf fs env f1) (evalf fs env f2)
evalb fs env (FLte f1 f2) = mapEval (<=) (evalf fs env f1) (evalf fs env f2)
evalb fs env (SEql s1 s2) = mapEval (==) (evals fs env s1) (evals fs env s2)
evalb fs env (BApp fn es) = case evalFunc fs fn es env of
                              Right err -> Right err
                              Left val -> case val of
                                            BoolVal n -> Left n
                                            otherwise -> Right $ "Function " ++ fn ++ " returned invalid type"

data Instr = IAssign VarName IExpr
           | FAssign VarName FExpr
           | SAssign VarName SExpr
           | BAssign VarName BExpr
           | IfElse BExpr Instr Instr
           | If BExpr Instr
           | While BExpr Instr
           | For Instr BExpr Instr Instr
           | Do [Instr]
           | DefFunc String [Params] [Instr]
           | IReturn IExpr
           | FReturn FExpr
           | SReturn SExpr
           | BReturn BExpr
           | PrintLexicalError String
           | PrintParseError String
           | Nop
  deriving Show

execList :: [Func] -> [Instr] -> Env -> (Env, [Func])
execList fs [] env = (env, fs)
execList fs (ins:xs) env = let newstuff = (exec fs ins env) in
                              execList (snd newstuff) xs (fst newstuff)

exec :: [Func] -> Instr -> Env -> (Env, [Func])
exec fs (IAssign x exp) env = case (evali fs env exp) of
                                Left n -> (update (x, IntVal n) env, fs)
                                Right err -> (update ("", ErrVal err) env, fs)
exec fs (FAssign x exp) env = case (evalf fs env exp) of
                                Left n -> (update (x, FloatVal n) env, fs)
                                Right err -> (update ("", ErrVal err) env, fs)
exec fs (SAssign x exp) env = case (evals fs env exp) of
                                Left n -> (update (x, StringVal n) env, fs)
                                Right err -> (update ("", ErrVal err) env, fs)
exec fs (BAssign x exp) env = case (evalb fs env exp) of
                                Left n -> (update (x, BoolVal n) env, fs)
                                Right err -> (update ("", ErrVal err) env, fs)
exec fs (IfElse exp ins1 ins2) env = case evalb fs env exp of
                                      Left True -> exec fs ins1 env
                                      Left False -> exec fs ins2 env
                                      Right err -> (update ("", ErrVal err) env, fs)
exec fs (If exp ins) env = case evalb fs env exp of
                                      Left True -> exec fs ins env
                                      Left False -> (env, fs)
                                      Right err -> (update ("", ErrVal err) env, fs)
exec fs (While exp ins) env = case evalb fs env exp of
                                Left True -> let newstuff = (exec fs ins env) in
                                                            exec (snd newstuff) (While exp ins) (fst newstuff)
                                Left False -> (env, fs)
                                Right err -> (update ("", ErrVal err) env, fs)
exec fs (For init exp after ins) env = let newstuff = exec fs init env in
                                          case evalb (snd newstuff) (fst newstuff) exp of
                                            Left True -> exec (snd newstuff) (While exp (Do [ins, after])) (fst newstuff)
                                            Left False -> newstuff
                                            Right err -> (update ("", ErrVal err) env, fs)
exec fs (Do xs) env = execList fs xs env
exec fs (DefFunc fn params inss) env = (env, (fn, params, inss):fs)
exec fs (IReturn exp) env = case evali fs env exp of
                              Left n -> (update ("", IntVal n) env, fs)
                              Right err -> (update ("", ErrVal err) env, fs)
exec fs (FReturn exp) env = case evalf fs env exp of
                              Left n -> (update ("", FloatVal n) env, fs)
                              Right err -> (update ("", ErrVal err) env, fs)
exec fs (SReturn exp) env = case evals fs env exp of
                              Left n -> (update ("", StringVal n) env, fs)
                              Right err -> (update ("", ErrVal err) env, fs)
exec fs (BReturn exp) env = case evalb fs env exp of
                              Left n -> (update ("", BoolVal n) env, fs)
                              Right err -> (update ("", ErrVal err) env, fs)
exec fs Nop env = (env, fs)

data Keywords = IfK | ElseK | WhileK | ForK | NopK | ReturnK
  deriving Show

data UOps = NotOp | LenOp | StrOp | FloorOp | FloatOp
  deriving Show
data BOps = AddOp | SubOp | MulOp | DivOp | ModOp | PowOp
          | AndOp | OrOp  | EqlOp | LtOp  | LteOp | CatOp
  deriving Show
data Token = FnSym String | VSym String | FSym Float
           | CSym Integer | BSym Bool | SSym String
           | LPar | RPar | LBra | RBra | Semi | Colon
           | Comma | LSq | RSq
           | UOp UOps | BOp BOps | AssignOp
           | Keyword Keywords
           | TCK Type
           | Err String
           | PI IExpr | PF FExpr | PS SExpr | PB BExpr
           | PIns Instr | Block [Instr] | Args [Value]
           | IAppT String [Expr]
           | FAppT String [Expr]
           | BAppT String [Expr]
           | SAppT String [Expr]
  deriving Show

isFloatChar :: Char -> Bool
isFloatChar x = isDigit x || x == '.'

count :: Eq a => a -> [a] -> Int
count x = length . filter (x==)

lexer :: String -> [Token]
lexer "" = []
lexer ('(':s) = LPar:(lexer s)
lexer (')':s) = RPar:(lexer s)
lexer ('{':s) = LBra:(lexer s)
lexer ('}':s) = RBra:(lexer s)
lexer ('[':s) = LSq:(lexer s)
lexer (']':s) = RSq:(lexer s)
lexer (',':s) = Comma:(lexer s)
lexer (';':s) = Semi:(lexer s)
lexer (':':s) = Colon:(lexer s)
lexer ('.':s) = (BOp CatOp):(lexer s)
lexer ('+':s) = (BOp AddOp):(lexer s)
lexer ('-':s) = (BOp SubOp):(lexer s)
lexer ('*':s) = (BOp MulOp):(lexer s)
lexer ('&':s) = (BOp AndOp):(lexer s)
lexer ('|':s) = (BOp OrOp):(lexer s)
lexer ('/':s) = (BOp DivOp):(lexer s)
lexer ('^':s) = (BOp PowOp):(lexer s)
lexer ('!':s) = (UOp NotOp):(lexer s)
lexer ('#':s) = (UOp LenOp):(lexer s)
lexer ('l':'e':'n':s) = (UOp LenOp):(lexer s)
lexer ('s':'t':'r':'v':'a':'l':s) = (UOp StrOp):(lexer s)
lexer ('f':'l':'o':'o':'r':s) = (UOp FloorOp):(lexer s)
lexer ('=':'=':s) = (BOp EqlOp):(lexer s)
lexer ('<':'=':s) = (BOp LteOp):(lexer s)
lexer ('<':s) = (BOp LtOp):(lexer s)
lexer ('=':s) = (AssignOp):(lexer s)
lexer ('w':'h':'i':'l':'e':s) = (Keyword WhileK):(lexer s)
lexer ('f':'o':'r':s) = (Keyword ForK):(lexer s)
lexer ('i':'f':s) = (Keyword IfK):(lexer s)
lexer ('e':'l':'s':'e':s) = (Keyword ElseK):(lexer s)
lexer ('n':'o':'p':s) = (Keyword NopK):(lexer s)
lexer ('r':'e':'t':'u':'r':'n':s) = (Keyword ReturnK):(lexer s)
lexer ('T':'r':'u':'e':s) = (BSym True):(lexer s)
lexer ('F':'a':'l':'s':'e':s) = (BSym False):(lexer s)
lexer ('i':'n':'t':s) = (TCK IntT):lexer s
lexer ('f':'l':'o':'a':'t':s) = (TCK FloatT):lexer s
lexer ('b':'o':'o':'l':'e':'a':'n':s) = (TCK BoolT):lexer s
lexer ('s':'t':'r':'i':'n':'g':s) = (TCK StringT):lexer s
lexer ('"':s) = (SSym vs):(lexer (drop 1 xs))
                          where (vs, xs) = span (/='"') s
lexer full@(c:s) | isLower c = (VSym vs):(lexer xs)
                          where (vs, xs) = span isAlphaNum full
lexer full@(c:s) | isUpper c = (FnSym vs):(lexer xs)
                          where (vs,xs) = span isAlphaNum full
lexer full@(n:s) | isDigit n = let (vs, xs) = span isFloatChar full in
                                  if count '.' vs == 1 && isDigit (last vs) then
                                    (FSym (read vs)):(lexer xs)
                                  else if count '.' vs == 0 then
                                    (CSym (read vs)):(lexer xs)
                                  else [Err full]
lexer (w:s) | isSpace w = lexer s
lexer s = [Err s]

isInstr :: Token -> Bool
isInstr t = case t of
              PIns _ -> True
              otherwise -> False
isSemi :: Token -> Bool
isSemi t = case t of
            Semi -> True
            otherwise -> False
isNotElse :: Token -> Bool
isNotElse t = case t of
                Keyword ElseK -> False
                otherwise -> True

sr :: [Token] -> [Token] -> [TypeConstr] -> [Token]
sr (VSym v:TCK t:PIns (DefFunc fn ps []):st) (c:q) tc = sr (c:VSym v:TCK t:PIns (DefFunc fn ps []):st) q tc
sr (VSym v:st) (c1:q) tc = case c1 of
                          AssignOp -> sr (c1:VSym v:st) q tc
                          otherwise -> case lookup v tc of
                            Nothing -> [Err $ "Undeclared Variable " ++ v]
                            Just IntT -> sr (PI (IVar v):st) (c1:q) tc
                            Just FloatT -> sr (PF (FVar v):st) (c1:q) tc
                            Just BoolT -> sr (PB (BVar v):st) (c1:q) tc
                            Just StringT -> sr (PS (SVar v):st) (c1:q) tc

sr (LPar:FnSym fn:TCK t:st) q tc = sr (PIns (DefFunc fn [] []):st) q ((fn,t):tc)
sr (Comma:VSym v:TCK t:PIns (DefFunc fn ps []):st) q tc = sr (PIns (DefFunc fn (ps ++ [(v, t)]) []):st) q ((v,t):tc)
sr (RPar:VSym v:TCK t:PIns (DefFunc fn ps []):st) q tc = sr (PIns (DefFunc fn (ps ++ [(v, t)]) []):st) q ((v,t):tc)
sr (PIns (Do is):PIns (DefFunc fn ps []):st) q tc = sr (PIns (DefFunc fn ps [Do is]):st) q (removeUntil (head ps) tc)

sr (BSym True:st) q tc = sr (PB TT:st) q tc
sr (BSym False:st) q tc = sr (PB FF:st) q tc
sr (CSym n:st) q tc = sr (PI (IConst n):st) q tc
sr (FSym n:st) q tc = sr (PF (FConst n):st) q tc
sr (SSym s:st) q tc = sr (PS (SConst s):st) q tc

sr (PI i2:BOp AddOp:PI i1:st) q tc = sr (PI (Add i1 i2):st) q tc
sr (PI i2:BOp SubOp:PI i1:st) q tc = sr (PI (Sub i1 i2):st) q tc
sr (PI i2:BOp MulOp:PI i1:st) q tc = sr (PI (Mul i1 i2):st) q tc
sr (PI i2:BOp DivOp:PI i1:st) q tc = sr (PI (Div i1 i2):st) q tc
sr (PI i2:BOp ModOp:PI i1:st) q tc = sr (PI (Mod i1 i2):st) q tc
sr (PI i2:BOp PowOp:PI i1:st) q tc = sr (PI (Pow i1 i2):st) q tc
sr (PS s:UOp LenOp:st) q tc = sr (PI (Len s):st) q tc
sr (PF f:UOp FloorOp:st) q tc = sr (PI (Floor f):st) q tc
sr (RPar:PI i:LPar:st) q tc = sr (PI i:st) q tc
sr (LPar:FnSym fn:st) q tc | lookup fn tc == Just IntT = sr ((IAppT fn []):st) q tc
sr (Comma:PI i:(IAppT fn ps):st) q tc = sr ((IAppT fn (ps ++ [IEx i])):st) q tc
sr (RPar:PI i:(IAppT fn ps):st) q tc = sr (PI (IApp fn (ps ++ [IEx i])):st) q tc
sr (Comma:PB i:(IAppT fn ps):st) q tc = sr ((IAppT fn (ps ++ [BEx i])):st) q tc
sr (RPar:PB i:(IAppT fn ps):st) q tc = sr (PI (IApp fn (ps ++ [BEx i])):st) q tc
sr (Comma:PF i:(IAppT fn ps):st) q tc = sr ((IAppT fn (ps ++ [FEx i])):st) q tc
sr (RPar:PF i:(IAppT fn ps):st) q tc = sr (PI (IApp fn (ps ++ [FEx i])):st) q tc
sr (Comma:PS i:(IAppT fn ps):st) q tc = sr ((IAppT fn (ps ++ [SEx i])):st) q tc
sr (RPar:PS i:(IAppT fn ps):st) q tc = sr (PI (IApp fn (ps ++ [SEx i])):st) q tc

sr (PF f2:BOp AddOp:PF f1:st) q tc = sr (PF (FAdd f1 f2):st) q tc
sr (PF f2:BOp SubOp:PF f1:st) q tc = sr (PF (FSub f1 f2):st) q tc
sr (PF f2:BOp MulOp:PF f1:st) q tc = sr (PF (FMul f1 f2):st) q tc
sr (PF f2:BOp DivOp:PF f1:st) q tc = sr (PF (FDiv f1 f2):st) q tc
sr (PI i:TCK FloatT:st) q tc = sr (PF (ItoFloat i):st) q tc
sr (RPar:PF f:LPar:st) q tc = sr (PF f:st) q tc
sr (LPar:FnSym fn:st) q tc | lookup fn tc == Just FloatT = sr ((FAppT fn []):st) q tc
sr (Comma:PF f:(FAppT fn ps):st) q tc = sr ((FAppT fn (ps ++ [FEx f])):st) q tc
sr (RPar:PF f:(FAppT fn ps):st) q tc = sr (PF (FApp fn (ps ++ [FEx f])):st) q tc
sr (Comma:PB f:(FAppT fn ps):st) q tc = sr ((FAppT fn (ps ++ [BEx f])):st) q tc
sr (RPar:PB f:(FAppT fn ps):st) q tc = sr (PF (FApp fn (ps ++ [BEx f])):st) q tc
sr (Comma:PI f:(FAppT fn ps):st) q tc = sr ((FAppT fn (ps ++ [IEx f])):st) q tc
sr (RPar:PI f:(FAppT fn ps):st) q tc = sr (PF (FApp fn (ps ++ [IEx f])):st) q tc
sr (Comma:PS f:(FAppT fn ps):st) q tc = sr ((FAppT fn (ps ++ [SEx f])):st) q tc
sr (RPar:PS f:(FAppT fn ps):st) q tc = sr (PF (FApp fn (ps ++ [SEx f])):st) q tc

sr (PB b2:BOp AndOp:PB b1:st) q tc = sr (PB (And b1 b2):st) q tc
sr (PB b2:BOp OrOp:PB b1:st) q tc = sr (PB (Or b1 b2):st) q tc
sr (PB b:UOp NotOp:st) q tc = sr (PB (Not b):st) q tc
sr (PS s2:BOp EqlOp:PS s1:st) q tc = sr (PB (SEql s1 s2):st) q tc
sr (PI i2:BOp EqlOp:PI i1:st) q tc = sr (PB (IEql i1 i2):st) q tc
sr (PI i2:BOp LtOp:PI i1:st) q tc = sr (PB (ILt i1 i2):st) q tc
sr (PI i2:BOp LteOp:PI i1:st) q tc = sr (PB (ILte i1 i2):st) q tc
sr (PF f2:BOp EqlOp:PF f1:st) q tc = sr (PB (FEql f1 f2):st) q tc
sr (PF f2:BOp LtOp:PF f1:st) q tc = sr (PB (FLt f1 f2):st) q tc
sr (PF f2:BOp LteOp:PF f1:st) q tc = sr (PB (FLte f1 f2):st) q tc
sr (RPar:PF f:LPar:st) q tc = sr (PF f:st) q tc
sr (LPar:FnSym fn:st) q tc | lookup fn tc == Just BoolT = sr ((BAppT fn []):st) q tc
sr (Comma:PB b:(BAppT fn ps):st) q tc = sr ((BAppT fn (ps ++ [BEx b])):st) q tc
sr (RPar:PB b:(BAppT fn ps):st) q tc = sr (PB (BApp fn (ps ++ [BEx b])):st) q tc
sr (Comma:PF b:(BAppT fn ps):st) q tc = sr ((BAppT fn (ps ++ [FEx b])):st) q tc
sr (RPar:PF b:(BAppT fn ps):st) q tc = sr (PB (BApp fn (ps ++ [FEx b])):st) q tc
sr (Comma:PI b:(BAppT fn ps):st) q tc = sr ((BAppT fn (ps ++ [IEx b])):st) q tc
sr (RPar:PI b:(BAppT fn ps):st) q tc = sr (PB (BApp fn (ps ++ [IEx b])):st) q tc
sr (Comma:PS b:(BAppT fn ps):st) q tc = sr ((BAppT fn (ps ++ [SEx b])):st) q tc
sr (RPar:PS b:(BAppT fn ps):st) q tc = sr (PB (BApp fn (ps ++ [SEx b])):st) q tc


sr (PS s:st) (LSq:q) tc = sr (LSq:PS s:st) q tc
sr (PS s2:BOp CatOp:PS s1:st) q tc = sr (PS (Cat s1 s2):st) q tc
sr (PI i:UOp StrOp:st) q tc = sr (PS (ItoString i):st) q tc
sr (PF f:UOp StrOp:st) q tc = sr (PS (FtoString f):st) q tc
sr (PB b:UOp StrOp:st) q tc = sr (PS (BtoString b):st) q tc
sr (RSq:PI i:LSq:PS str:st) q tc = sr (PS (Idx str i):st) q tc
sr (RSq:PI i2:Colon:PI i1:LSq:PS str:st) q tc = sr (PS (Slc str i1 i2):st) q tc
sr (RPar:PS str:LPar:st) q tc = sr (PS str:st) q tc
sr (LPar:FnSym fn:st) q tc | lookup fn tc == Just StringT = sr ((SAppT fn []):st) q tc
sr (Comma:PS s:(SAppT fn ps):st) q tc = sr ((SAppT fn (ps ++ [SEx s])):st) q tc
sr (RPar:PS s:(SAppT fn ps):st) q tc = sr (PS (SApp fn (ps ++ [SEx s])):st) q tc
sr (Comma:PB s:(SAppT fn ps):st) q tc = sr ((SAppT fn (ps ++ [BEx s])):st) q tc
sr (RPar:PB s:(SAppT fn ps):st) q tc = sr (PS (SApp fn (ps ++ [BEx s])):st) q tc
sr (Comma:PI s:(SAppT fn ps):st) q tc = sr ((SAppT fn (ps ++ [IEx s])):st) q tc
sr (RPar:PI s:(SAppT fn ps):st) q tc = sr (PS (SApp fn (ps ++ [IEx s])):st) q tc
sr (Comma:PF s:(SAppT fn ps):st) q tc = sr ((SAppT fn (ps ++ [FEx s])):st) q tc
sr (RPar:PF s:(SAppT fn ps):st) q tc = sr (PS (SApp fn (ps ++ [FEx s])):st) q tc

sr (LPar:FnSym fn:st) q tc | lookup fn tc == Nothing = [Err $ "Function " ++ fn ++ " undefined"]


sr (Semi:PI exp:AssignOp:VSym v:TCK t:st) q tc = case lookup v tc of
                                                    Nothing -> if t /= IntT then
                                                                  [Err $ "Unable to assign Integer value to " ++ (show t) ++ " variable " ++ v]
                                                               else
                                                                  sr (PIns (IAssign v exp):st) q ((v, t):tc)
                                                    something -> [Err $ "Variable " ++ v ++ " already declared"]
sr (Keyword ElseK:PI exp:AssignOp:VSym v:TCK t:st) q tc = case lookup v tc of
                                                    Nothing -> if t /= IntT then
                                                                  [Err $ "Unable to assign Integer value to " ++ (show t) ++ " variable " ++ v]
                                                               else
                                                                  sr (Keyword ElseK:PIns (IAssign v exp):st) q ((v, t):tc)
                                                    something -> [Err $ "Variable " ++ v ++ " already declared"]
sr (Semi:PB exp:AssignOp:VSym v:TCK t:st) q tc = case lookup v tc of
                                                    Nothing -> if t /= BoolT then
                                                                  [Err $ "Unable to assign Boolean value to " ++ (show t) ++ " variable " ++ v]
                                                               else
                                                                  sr (PIns (BAssign v exp):st) q ((v, t):tc)
                                                    something -> [Err $ "Variable " ++ v ++ " already declared"]
sr (Keyword ElseK:PB exp:AssignOp:VSym v:TCK t:st) q tc = case lookup v tc of
                                                    Nothing -> if t /= BoolT then
                                                                  [Err $ "Unable to assign Boolean value to " ++ (show t) ++ " variable " ++ v]
                                                               else
                                                                  sr (Keyword ElseK:PIns (BAssign v exp):st) q ((v, t):tc)
                                                    something -> [Err $ "Variable " ++ v ++ " already declared"]
sr (Semi:PF exp:AssignOp:VSym v:TCK t:st) q tc = case lookup v tc of
                                                    Nothing -> if t /= FloatT then
                                                                  [Err $ "Unable to assign Float value to " ++ (show t) ++ " variable " ++ v]
                                                               else
                                                                  sr (PIns (FAssign v exp):st) q ((v, t):tc)
                                                    something -> [Err $ "Variable " ++ v ++ " already declared"]
sr (Keyword ElseK:PF exp:AssignOp:VSym v:TCK t:st) q tc = case lookup v tc of
                                                    Nothing -> if t /= FloatT then
                                                                  [Err $ "Unable to assign Float value to " ++ (show t) ++ " variable " ++ v]
                                                               else
                                                                  sr (Keyword ElseK:PIns (FAssign v exp):st) q ((v, t):tc)
                                                    something -> [Err $ "Variable " ++ v ++ " already declared"]
sr (Semi:PS exp:AssignOp:VSym v:TCK t:st) q tc = case lookup v tc of
                                                    Nothing -> if t /= StringT then
                                                                  [Err $ "Unable to assign String value to " ++ (show t) ++ " variable " ++ v]
                                                               else
                                                                  sr (PIns (SAssign v exp):st) q ((v, t):tc)
                                                    something -> [Err $ "Variable " ++ v ++ " already declared"]
sr (Keyword ElseK:PS exp:AssignOp:VSym v:TCK t:st) q tc = case lookup v tc of
                                                    Nothing -> if t /= StringT then
                                                                  [Err $ "Unable to assign String value to " ++ (show t) ++ " variable " ++ v]
                                                               else
                                                                  sr (Keyword ElseK:PIns (SAssign v exp):st) q ((v, t):tc)
                                                    something -> [Err $ "Variable " ++ v ++ " already declared"]
sr (Semi:PI exp:AssignOp:VSym v:st) q tc = case lookup v tc of
                                              Nothing -> [Err $ "Cannot assign value to undeclared variable " ++ v]
                                              Just IntT -> sr (PIns (IAssign v exp):st) q tc
                                              Just otherwise -> [Err $ "Cannot assign Integer value to " ++ (show otherwise) ++ " variable " ++ v]
sr (Keyword ElseK:PI exp:AssignOp:VSym v:st) q tc = case lookup v tc of
                                              Nothing -> [Err $ "Cannot assign value to undeclared variable " ++ v]
                                              Just IntT -> sr (Keyword ElseK:PIns (IAssign v exp):st) q tc
                                              Just otherwise -> [Err $ "Cannot assign Integer value to " ++ (show otherwise) ++ " variable " ++ v]
sr (Semi:PB exp:AssignOp:VSym v:st) q tc = case lookup v tc of
                                              Nothing -> [Err $ "Cannot assign value to undeclared variable " ++ v]
                                              Just BoolT -> sr (PIns (BAssign v exp):st) q tc
                                              Just otherwise -> [Err $ "Cannot assign Boolean value to " ++ (show otherwise) ++ " variable " ++ v]
sr (Keyword ElseK:PB exp:AssignOp:VSym v:st) q tc = case lookup v tc of
                                              Nothing -> [Err $ "Cannot assign value to undeclared variable " ++ v]
                                              Just BoolT -> sr (Keyword ElseK:PIns (BAssign v exp):st) q tc
                                              Just otherwise -> [Err $ "Cannot assign Boolean value to " ++ (show otherwise) ++ " variable " ++ v]
sr (Semi:PF exp:AssignOp:VSym v:st) q tc = case lookup v tc of
                                              Nothing -> [Err $ "Cannot assign value to undeclared variable " ++ v]
                                              Just FloatT -> sr (PIns (FAssign v exp):st) q tc
                                              Just otherwise -> [Err $ "Cannot assign Float value to " ++ (show otherwise) ++ " variable " ++ v]
sr (Keyword ElseK:PF exp:AssignOp:VSym v:st) q tc = case lookup v tc of
                                              Nothing -> [Err $ "Cannot assign value to undeclared variable " ++ v]
                                              Just FloatT -> sr (Keyword ElseK:PIns (FAssign v exp):st) q tc
                                              Just otherwise -> [Err $ "Cannot assign Float value to " ++ (show otherwise) ++ " variable " ++ v]
sr (Semi:PS exp:AssignOp:VSym v:st) q tc = case lookup v tc of
                                              Nothing -> [Err $ "Cannot assign value to undeclared variable " ++ v]
                                              Just StringT -> sr (PIns (SAssign v exp):st) q tc
                                              Just otherwise -> [Err $ "Cannot assign String value to " ++ (show otherwise) ++ " variable " ++ v]
sr (Keyword ElseK:PS exp:AssignOp:VSym v:st) q tc = case lookup v tc of
                                              Nothing -> [Err $ "Cannot assign value to undeclared variable " ++ v]
                                              Just StringT -> sr (Keyword ElseK:PIns (SAssign v exp):st) q tc
                                              Just otherwise -> [Err $ "Cannot assign String value to " ++ (show otherwise) ++ " variable " ++ v]

sr (LBra:st) q tc = sr (Block []:st) q tc
sr (PIns i:Block xs:st) q tc = sr (Block (xs ++ [i]):st) q tc
sr (RBra:Block xs:st) q tc = sr (PIns (Do xs):st) q tc

sr (Semi:PI i:Keyword ReturnK:st) q tc = sr (PIns (IReturn i):st) q tc
sr (Keyword ElseK:PI i:Keyword ReturnK:st) q tc = sr (Keyword ElseK:PIns (IReturn i):st) q tc
sr (Semi:PB i:Keyword ReturnK:st) q tc = sr (PIns (BReturn i):st) q tc
sr (Keyword ElseK:PB i:Keyword ReturnK:st) q tc = sr (Keyword ElseK:PIns (BReturn i):st) q tc
sr (Semi:PF i:Keyword ReturnK:st) q tc = sr (PIns (FReturn i):st) q tc
sr (Keyword ElseK:PF i:Keyword ReturnK:st) q tc = sr (Keyword ElseK:PIns (FReturn i):st) q tc
sr (Semi:PS i:Keyword ReturnK:st) q tc = sr (PIns (SReturn i):st) q tc
sr (Keyword ElseK:PS i:Keyword ReturnK:st) q tc = sr (Keyword ElseK:PIns (SReturn i):st) q tc

sr (Semi:Keyword NopK:st) q tc = sr (PIns (Nop):st) q tc
sr (Keyword ElseK:Keyword NopK:st) q tc = sr (Keyword ElseK:PIns (Nop):st) q tc

sr (PIns ins:PB b:Keyword WhileK:st) q tc = sr (PIns (While b ins):st) q tc
sr (PIns ins:RPar:PIns i2:Semi:PB b:PIns i1:LPar:Keyword ForK:st) q tc = sr (PIns (For i1 b i2 ins):st) q tc

sr (PIns i2:Keyword ElseK:PIns i1:PB b:Keyword IfK:st) q tc = sr (PIns (IfElse b i1 i2):st) q tc

sr (PIns i:PB b:Keyword IfK:st) (c:q) tc | isNotElse c = sr (PIns (If b i):st) q tc

sr xs (next:q) tc = sr (next:xs) q tc
sr xs [] tc = xs

getInstr :: Token -> Instr
getInstr (PIns i) = i
getInstr _ = error "should never happen"

getInstrs :: [Token] -> [Instr]
getInstrs = map getInstr

getErrors :: [Token] -> String
getErrors [] = ""
getErrors (Err s:xs) = s ++ "\n" ++ getErrors xs
getErrors (_:xs) = getErrors xs

parser :: String -> Either [Instr] Error
parser s = let redd = sr [] (lexer s) [] in
              if all isInstr redd then Left $ reverse (getInstrs redd)
              else Right $ show redd

returnValues :: Env -> String
returnValues e = drop 1 (returnValues' e)

returnValues' :: Env -> String
returnValues' [] = ""
returnValues' ((v,val):xs) | not (all isDigit v) = returnValues' xs
returnValues' ((v,val):xs) = returnValues' xs ++ "\n" ++ (case val of
                              IntVal n -> show n
                              FloatVal f -> show f
                              BoolVal b -> show b
                              StringVal s -> s
                              ErrVal s -> s
                                )

main :: IO ()
main = rep

rep :: IO ()
rep = do
        putStr "File to read: "
        fileName <- getLine
        handle <- openFile fileName ReadMode
        contents <- hGetContents handle
        prog <- return $ parser contents
        case prog of
          Right err -> putStrLn err
          Left ls -> do
            out <- return (execList [] ls [])
            putStrLn $ (returnValues (fst out))
        hClose handle

reptest :: IO ()
reptest = do
        putStr "File to read: "
        fileName <- getLine
        handle <- openFile fileName ReadMode
        contents <- hGetContents handle
        prog <- return $ parser contents
        case prog of
          Right err -> putStrLn err
          Left ls -> do
            out <- return ls
            putStrLn $ show out
        hClose handle
