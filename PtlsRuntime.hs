module PtlsRuntime (module PtlsRuntime, module Data.Dynamic, module Data.Maybe) where

import Debug.Trace
import Data.Char
import Data.List
import System.Random
import System.IO.Unsafe
import Data.Hashable
import Data.Dynamic
import Data.Maybe
import qualified Data.Vector as Vector
import qualified Data.Map.Strict as StrictMap

data Location = PtlsLocation{ln :: Int, cn :: Int, fn :: String}
data Locateable a = PtlsLocated{value :: a, location :: Location}

instance Show a => Show (Locateable a) where
  show (PtlsLocated a loc) = show loc ++ "\n" ++ show a

instance Show Location where
  show (PtlsLocation ln cn fn) = "At line no: " ++ show ln ++ ", col no: " ++ show cn ++ " in '" ++ fn ++ "'"

createLocateable a loc = PtlsLocated{value = a, location = loc}
createLocation ln cn fn = PtlsLocation{ln = ln, cn = cn, fn = fn}

drill f v =
  let
    opener (PtlsLocated opnd loc) = createLocateable (f opnd) loc
  in
    opener v

data Value =
  PtlsString{strValue :: Locateable String}
  | PtlsBool{boolValue :: Locateable Bool}
  | PtlsNumber{numValue :: Locateable Float}
  | PtlsBuiltIn{signature :: String, builtIn :: Locateable (Value -> Value)}
  | PtlsDict{dictValue :: Locateable (StrictMap.Map Int Value), showDictValue :: [(Value, Value)]}
  | PtlsSet{setValue :: Locateable (StrictMap.Map Int Value)}
  | PtlsFunc{func :: Locateable (Value -> Value)}
  | PtlsException{exc :: Value}
  | PtlsTuple{tup :: Dynamic, lisVersion :: Locateable [Value], tupLabel :: Value, len :: Int}
  | PtlsArray{arr :: Locateable (Vector.Vector Value)}
  | PtlsList {listValue :: Locateable [Value]}
  | PtlsLabel{labelValue :: Locateable String}
  | PtlsObject{objValue :: Locateable (StrictMap.Map Int Value), showObj :: [(String, Value)], objLabel :: Value}
  deriving (Typeable)

getLocation :: Value -> Location
getLocation (PtlsString (PtlsLocated _ loc)) = loc
getLocation (PtlsBool (PtlsLocated _ loc)) = loc
getLocation (PtlsNumber (PtlsLocated _ loc)) = loc
getLocation (PtlsBuiltIn _ (PtlsLocated _ loc)) = loc
getLocation (PtlsDict (PtlsLocated _ loc) _) = loc
getLocation (PtlsSet (PtlsLocated _ loc)) = loc
getLocation (PtlsFunc (PtlsLocated _ loc)) = loc
getLocation (PtlsException e) = getLocation e
getLocation (PtlsTuple _ (PtlsLocated _ loc) _ _) = loc
getLocation (PtlsArray (PtlsLocated _ loc)) = loc
getLocation (PtlsList (PtlsLocated _ loc)) = loc
getLocation (PtlsLabel (PtlsLocated _ loc)) = loc
getLocation (PtlsObject (PtlsLocated _ loc) _ _) = loc

unterminatedListValue :: Location -> [Value] -> [Value]
unterminatedListValue loc (x:xs) = filter (\x -> not (is_ptlsTrue (x `ptlsEquals` createLabel loc "Empty"))) l where l = x : xs

getList (PtlsList (PtlsLocated l loc)) = l
getList a = error (show (createException (createString (getLocation a) (show a ++ " is not a list"))))

getTuple (PtlsTuple t _ _ _) = t
getTuple nt = error(show (createException(createString (getLocation nt) (show nt ++ " is not a tuple"))))

instance Show Value where
  show (PtlsString s) = value s
  show (PtlsNumber n) = show (value n)
  show (PtlsBuiltIn s _) = s
  show (PtlsBool b) = if value b then "true" else "false"
  show (PtlsException e) = trace("\"" ++ show (getLocation e) ++ "\"") ("Exception: " ++ show e ++ "\n" ++ show (getLocation e))
  show (PtlsTuple _ lis l _) = show l ++ "(" ++ listToString (value lis) show ", " ++ ")"
  show (PtlsFunc _) = "<function>"
  show (PtlsDict _ d) = "{" ++ listToString d (\(k, v) -> show k ++ ": " ++ show v) ", " ++ "}"
  show (PtlsObject _ o l) = show l ++ "{" ++ listToString o (\(k, v) -> k ++ " = " ++ show v) ", " ++ "}"
  show (PtlsArray a) = "[" ++ listToString (Vector.toList (value a)) show " " ++ "]"
  show (PtlsList l) = "[" ++ (listToString (filter (\x -> not (is_ptlsTrue (x `ptlsEquals` (createLabel (location l) "Empty")))) (value l)) show ", ") ++ "]"
  show (PtlsSet s) = "{" ++ listToString (StrictMap.toList (value s)) (\(_, v) -> show v) ", " ++ "}"
  show (PtlsLabel lb) = if value lb == "Empty" then "[]" else value lb

instance Eq Value where
  (PtlsString a) == (PtlsString b) = value a == value b
  (PtlsNumber a) == (PtlsNumber b) = value a == value b
  (PtlsBool a) == (PtlsBool b) = value a == value  b
  (PtlsLabel a) == (PtlsLabel b) = value a == value b
  (PtlsFunc a) == (PtlsFunc b) = False
  a == b = False

-- Hashable Instance
instance Hashable Value where
  hashWithSalt sa (PtlsNumber n) = sa `hashWithSalt` value n
  hashWithSalt sa (PtlsString s) = sa `hashWithSalt` value s
  hashWithSalt sa (PtlsBool b) = sa `hashWithSalt` value b
  hashWithSalt sa (PtlsLabel lb) = sa `hashWithSalt` value lb
  hashWithSalt sa (PtlsTuple _ (PtlsLocated [a] _) _ _) = sa `hashWithSalt` hash a
  hashWithSalt sa (PtlsTuple _ (PtlsLocated (x:xs) _) lab _) = (sa `hashWithSalt` x) + (sa `hashWithSalt` xs) + hash lab

  hash (PtlsNumber n) = 1111 `hashWithSalt` value n
  hash (PtlsString s) = 2222 `hashWithSalt` value s
  hash (PtlsBool b) = 10 `hashWithSalt` value b
  hash (PtlsLabel lb) = 107 `hashWithSalt` value lb
  hash (PtlsTuple tup (PtlsLocated (x:xs) loc) lab len) = 193 `hashWithSalt` createLabeledTuple tup len (createLocateable (x:xs) loc) (value (labelValue lab))

-- Helpers

eqList a b f loc =
  let
    zipped = zipWith f a b
    true = createBool loc True
    folded = foldl ptlsAnd true zipped
  in
    folded

listToString l f sep = intercalate sep (map f l)

createNumber loc n = PtlsNumber{numValue = createLocateable n loc}
createBool loc b = PtlsBool{boolValue = createLocateable b loc}
createBuiltIn loc s f = PtlsBuiltIn{signature = s, builtIn = createLocateable f loc}
createString loc s = PtlsString{strValue = createLocateable s loc}
createException e = PtlsException{exc = e}
createFunc loc f = PtlsFunc{func = createLocateable f loc}
createTuple loc t l lis = PtlsTuple{tup = t, len = l, tupLabel = createLabel loc "PtlsTuple", lisVersion = createLocateable lis loc}
createArray loc a = PtlsArray{arr = createLocateable (Vector.fromList a) loc}
createList loc l = PtlsList{listValue = createLocateable (l ++ [createLabel loc "Empty"]) loc}
createLabel loc l = PtlsLabel{labelValue = createLocateable l loc}
createSet loc s =
  let
    hs = map (\v -> (hash v, v)) s
  in
    PtlsSet{setValue = createLocateable (StrictMap.fromList hs) loc}
createDict loc d =
  let
    hd = map (\(k, v) -> (hash k, v)) d
  in
    PtlsDict{dictValue = createLocateable (StrictMap.fromList hd) loc, showDictValue = d}
createObject loc o =
  let
    ho = map (\(k, v) -> (hash k, v)) o
  in
    PtlsObject{objValue = createLocateable (StrictMap.fromList ho) loc, showObj = o, objLabel = createLabel loc "PtlsObject"}

copyLocatable (PtlsLocated a loc) = createLocateable a loc

internalCreateSet s = PtlsSet{setValue = copyLocatable s}
createTerminatedList l = PtlsList{listValue = PtlsLocated{value = value l, location = location l}}
createLabeledTuple t len lis lab = PtlsTuple{tup = t, len = len, tupLabel = createLabel (location lis) lab, lisVersion = copyLocatable lis}
createLabeledObject o so lab = PtlsObject{objValue = copyLocatable o, showObj = so, objLabel = createLabel (location o) lab}
internalCreateDict d l = PtlsDict{dictValue = copyLocatable d, showDictValue = l}
internalCreateObject o so lb = PtlsObject{objValue = copyLocatable o, showObj = so, objLabel = lb}
internalCreateArray arr = PtlsArray{arr = copyLocatable arr}

ptlsEquals a@(PtlsException _) _ = a
ptlsEquals _ b@(PtlsException _) = b
ptlsEquals (PtlsArray (PtlsLocated a1 loc1)) (PtlsArray (PtlsLocated a2 loc2)) =
  if Vector.length a1 /= Vector.length a2 then createBool loc1 False
  else eqList (Vector.toList a1) (Vector.toList a2) ptlsEquals loc1
ptlsEquals (PtlsList (PtlsLocated l1 loc1)) (PtlsList (PtlsLocated l2 loc2)) =
  if length l1 /= length l2 then createBool loc1 False
  else eqList l1 l2 ptlsEquals loc1
ptlsEquals (PtlsSet (PtlsLocated s1 loc1)) (PtlsSet (PtlsLocated s2 loc2)) =
  let
    l1 = StrictMap.toList s1
    l2 = StrictMap.toList s2
    equality (_, a) (_, b) = a `ptlsEquals` b
  in
    if length l1 /= length l2 then createBool loc1 False
    else eqList l1 l2 equality loc1
ptlsEquals (PtlsDict (PtlsLocated _ loc1) d1) (PtlsDict (PtlsLocated _ loc2) d2) =
  let
    equality (x1, y1) (x2, y2) = (x1 `ptlsEquals` x2) `ptlsAnd` (y1 `ptlsEquals` y2)
  in
    if length d1 /= length d2 then createBool loc1 False
    else eqList d1 d2 equality loc1
ptlsEquals (PtlsObject (PtlsLocated _ loc1) o1 _) (PtlsObject (PtlsLocated _ loc2) o2 _) =
  let
    equality (x1, y1) (x2, y2) = createBool loc1 (x1 == x2) `ptlsAnd` (y1 `ptlsEquals` y2)
  in
    if length o1 /= length o2 then createBool loc1 False
    else eqList o1 o2 equality loc1
ptlsEquals (PtlsTuple _ (PtlsLocated dl1 loc1) lb1 l1) (PtlsTuple _ (PtlsLocated dl2 loc2) lb2 l2) =
  if lb1 /= lb2 || l1 /= l2 then createBool loc1 False
  else eqList dl1 dl2 ptlsEquals loc1

ptlsEquals a b = createBool (getLocation a) (a == b)

ptlsNotEquals :: Value -> Value -> Value
ptlsNotEquals a@(PtlsException _) b = a
ptlsNotEquals a b@(PtlsException _) = b
ptlsNotEquals a b = ptlsNot (a `ptlsEquals` b)

ptlsNot :: Value -> Value
ptlsNot (PtlsBool (PtlsLocated b loc)) = createBool loc (not b)
ptlsNot e@(PtlsException _) = e
ptlsNot b = createException (createString (getLocation b) ("Can't negate " ++ show b))

ptlsLessThan :: Value -> Value -> Value
ptlsLessThan (PtlsNumber (PtlsLocated a loc)) (PtlsNumber (PtlsLocated b _)) = createBool loc (a < b)
ptlsLessThan a@(PtlsException _) b = a
ptlsLessThan a b@(PtlsException _) = b
ptlsLessThan a b = createException (createString (getLocation a) ("Can't check '<' of " ++ show a ++ " with " ++ show b))

ptlsLessEquals :: Value -> Value -> Value
ptlsLessEquals (PtlsNumber (PtlsLocated a loc)) (PtlsNumber (PtlsLocated b _)) = createBool loc (a <= b)
ptlsLessEquals a@(PtlsException _) b = a
ptlsLessEquals a b@(PtlsException _) = b
ptlsLessEquals a b = createException (createString (getLocation a) ("Can't check '<=' of " ++ show a ++ " with " ++ show b))

ptlsGreaterThan :: Value -> Value -> Value
ptlsGreaterThan (PtlsNumber (PtlsLocated a loc)) (PtlsNumber (PtlsLocated b _)) = createBool loc (a > b)
ptlsGreaterThan a@(PtlsException _) b = a
ptlsGreaterThan a b@(PtlsException _) = b
ptlsGreaterThan a b = createException (createString (getLocation a) ("Can't check '>' of " ++ show a ++ " with " ++ show b))

ptlsGreaterEquals :: Value -> Value -> Value
ptlsGreaterEquals (PtlsNumber (PtlsLocated a loc)) (PtlsNumber (PtlsLocated b _)) = createBool loc (a >= b)
ptlsGreaterEquals a@(PtlsException _) b = a
ptlsGreaterEquals a b@(PtlsException _) = b
ptlsGreaterEquals a b = createException (createString (getLocation a) ("Can't check '>=' of " ++ show a ++ " with " ++ show b))

ptlsNegate :: Value -> Value
ptlsNegate (PtlsNumber (PtlsLocated n loc)) = createNumber loc (n*(-1))
ptlsNegate e@(PtlsException _) = e
ptlsNegate n = createException (createString (getLocation n) ("Can't tell the '-' of " ++ show n))

ptlsAdd :: Value -> Value -> Value
ptlsAdd (PtlsNumber (PtlsLocated a loc)) (PtlsNumber (PtlsLocated b _)) = createNumber loc (a+b)
ptlsAdd (PtlsString (PtlsLocated a loc)) (PtlsString (PtlsLocated b _)) = createString loc (a++b)
ptlsAdd a@(PtlsException _) _ = a
ptlsAdd _ b@(PtlsException _) = b
ptlsAdd a b = createException (createString (getLocation a) ("Can't add " ++ show a ++ " with " ++ show b))

ptlsSub :: Value -> Value -> Value
ptlsSub (PtlsNumber (PtlsLocated a loc)) (PtlsNumber (PtlsLocated b _)) = createNumber loc (a-b)
ptlsSub a@(PtlsException _) b = a
ptlsSub a b@(PtlsException _) = b
ptlsSub a b = createException (createString (getLocation a) ("Can't subtract " ++ show a ++ " with " ++ show b))

ptlsMul :: Value -> Value -> Value
ptlsMul (PtlsNumber (PtlsLocated a loc)) (PtlsNumber (PtlsLocated b _)) = createNumber loc (a*b)
ptlsMul a@(PtlsException _) b = a
ptlsMul a b@(PtlsException _) = b
ptlsMul a b = createException (createString (getLocation a) ("Can't multiply " ++ show a ++ " with " ++ show b))

ptlsDiv :: Value -> Value -> Value
ptlsDiv (PtlsNumber (PtlsLocated a loc)) (PtlsNumber (PtlsLocated 0 _)) = createException (createString loc "Division by zero")
ptlsDiv (PtlsNumber (PtlsLocated a loc)) (PtlsNumber (PtlsLocated b _)) = createNumber loc (a/b)
ptlsDiv a@(PtlsException _) b = a
ptlsDiv a b@(PtlsException _) = b
ptlsDiv a b = createException (createString (getLocation a) ("Can't divide " ++ show a ++ " with " ++ show b))

ptlsMod :: Value -> Value -> Value
ptlsMod (PtlsNumber (PtlsLocated a loc)) (PtlsNumber (PtlsLocated b _)) = createNumber loc (a - (b*tmp)) where
  tmp :: Float
  tmp = fromIntegral (quot (round a) (round b))
ptlsMod a@(PtlsException _) b = a
ptlsMod a b@(PtlsException _) = b
ptlsMod a b = createException (createString (getLocation a) ("Can't modulus " ++ show a ++ " with " ++ show b))

ptlsPow :: Value -> Value -> Value
ptlsPow (PtlsNumber (PtlsLocated a loc)) (PtlsNumber (PtlsLocated b _)) = createNumber loc (a**b)
ptlsPow a@(PtlsException _) b = a
ptlsPow a b@(PtlsException _) = b
ptlsPow a b = createException (createString (getLocation a) ("Can't exponentiate " ++ show a ++ " with " ++ show b))

ptlsOr :: Value -> Value -> Value
ptlsOr (PtlsBool (PtlsLocated a loc)) (PtlsBool (PtlsLocated b _)) = createBool loc (a || b)
ptlsOr a@(PtlsException _) b = a
ptlsOr a b@(PtlsException _) = b
ptlsOr a b = createException (createString (getLocation a) ("Can't exponentiate " ++ show a ++ " with " ++ show b))

ptlsAnd :: Value -> Value -> Value
ptlsAnd (PtlsBool (PtlsLocated a loc)) (PtlsBool (PtlsLocated b _)) = createBool loc (a && b)
ptlsAnd a@(PtlsException _) b = a
ptlsAnd a b@(PtlsException _) = b
ptlsAnd a b = createException (createString (getLocation a) ("Can't exponentiate " ++ show a ++ " with " ++ show b))

is_ptlsTrue :: Value -> Bool
is_ptlsTrue (PtlsBool (PtlsLocated True loc)) = True
is_ptlsTrue (PtlsBool (PtlsLocated False loc)) = False
is_ptlsTrue (PtlsException e) = error (show (createException e))
is_ptlsTrue b = (error (show (createException b)))

execute :: Value -> Value -> Value
execute (PtlsFunc (PtlsLocated f _)) v = f v
execute (PtlsBuiltIn _ (PtlsLocated f _)) v = f v
execute f _ = createException (createString (getLocation f) ("Can't call " ++ show f))
f |> a = f `execute` a

isPtlsList (PtlsList (PtlsLocated lis loc)) = createList loc lis
isPtlsList a = error "Exception: 'output' definition is not a list"

getIfHasIndex (PtlsLocated m _) (PtlsLocated k loc) f =
  let
    h = hash (f k)
  in
    if StrictMap.member h m then m StrictMap.! h
    else createException (createString loc ("Can't get index " ++ show k))

getIndex :: Value -> Value -> Value
getIndex (PtlsDict m _) (PtlsNumber k) = getIfHasIndex m k (createNumber (location k))
getIndex (PtlsDict m _) (PtlsString k) = getIfHasIndex m k (createString (location k))
getIndex (PtlsDict m _) (PtlsBool k) = getIfHasIndex m k (createBool (location k))
getIndex (PtlsDict m _) (PtlsTuple tup (PtlsLocated lis location) (PtlsLabel lab) len) = getIfHasIndex m lab k where
  k = createLabeledTuple tup len (createLocateable lis location)
getIndex (PtlsArray (PtlsLocated a _)) (PtlsNumber (PtlsLocated b loc)) =
  case a Vector.!? round b of
    Just x -> x
    Nothing -> createException (createString loc ("Can't get index " ++ show b ++ " from " ++ show a))
getIndex (PtlsSet s) (PtlsNumber n) = getIfHasIndex s n (createNumber (location n))
getIndex (PtlsException a) b = createException a
getIndex a (PtlsException b) = createException b
getIndex m k = createException (createString (getLocation k) ("Can't get index " ++ show k ++ " from " ++ show m))

checkLabel l s a = if value (labelValue l) == s then a else error(show (createException (createString (getLocation l) ("Expected " ++ s ++ " but got " ++ show l))))

getProperty :: String -> Value -> Value
getProperty "!getLabel" (PtlsObject _ _ lb) = lb
getProperty "!getType" (PtlsObject (PtlsLocated _ loc) _ _) = createLabel loc "PtlsObject"
getProperty "!getDict" (PtlsObject (PtlsLocated _ loc) ol _) = createDict loc (map (\(k, v) -> (createString loc k, v)) ol)
getProperty p (PtlsObject o _ _) = getIfHasIndex o (createLocateable p (location o)) id

getProperty "!getList" (PtlsArray (PtlsLocated arr loc)) = createList loc (Vector.toList arr)
getProperty "!getType" (PtlsArray (PtlsLocated arr loc)) = createLabel loc "PtlsArray"
getProperty "!getLength" (PtlsArray (PtlsLocated arr loc)) = createNumber loc (fromIntegral (Vector.length arr))
getProperty "!getInt" (PtlsBool (PtlsLocated b loc)) = createNumber loc (if b then 1.0 else 0.0)
getProperty "!getFloat" (PtlsBool (PtlsLocated b loc)) = createNumber loc (if b then 1.0 else 0.0)
getProperty "!getString" (PtlsBool (PtlsLocated b loc)) = createString loc (show (createBool loc b))
getProperty "!getType" (PtlsBool (PtlsLocated b loc)) = createLabel loc "PtlsBool"
getProperty "!getType" (PtlsBuiltIn _ (PtlsLocated _ loc)) = createLabel loc "PtlsBuiltIn"
getProperty "!getDelKey" (PtlsDict (PtlsLocated d loc) sd) =
  createBuiltIn loc "!getDelKey(key)" (
    \k ->
      let
        delKeyFromList lis dk = filter (\(k, _) -> is_ptlsTrue(ptlsNot (k `ptlsEquals` dk))) lis
      in
        case k of
          (PtlsNumber (PtlsLocated _ loc)) -> createDict loc (delKeyFromList sd k)
          (PtlsString (PtlsLocated _ loc)) -> createDict loc (delKeyFromList sd k)
          (PtlsBool (PtlsLocated _ loc)) -> createDict loc (delKeyFromList sd k)
  )
getProperty "!getKeys" (PtlsDict (PtlsLocated d loc) sd) = createList loc (map fst sd)
getProperty "!getVals" (PtlsDict (PtlsLocated d loc) sd) = createList loc (map snd sd)
getProperty "!getType" (PtlsDict (PtlsLocated _ loc) _) = createLabel loc "PtlsDict"
getProperty "!getLength" (PtlsDict (PtlsLocated d loc) _) = createNumber loc (fromIntegral (length (StrictMap.toList d)))
getProperty "!getType" (PtlsFunc (PtlsLocated _ loc)) = createLabel loc "PtlsFunc"
getProperty "!getZeroes" (PtlsLabel (PtlsLocated l loc)) =
  checkLabel (createLabel loc l) "PtlsArray" (createBuiltIn loc "!getZeros(n)" (
      \i ->
        case i of
          (PtlsNumber (PtlsLocated n loc)) ->
            let
              array ci = if n <= ci then [] else [createNumber loc 0] ++ (array (ci+1))
            in
              createArray loc (array 0)
          _ -> createException(createString loc "n must be a number")
    )
  )
getProperty "!getWrapTuple" (PtlsLabel  (PtlsLocated s loc)) =
  createBuiltIn loc "!getWrapTuple(tuple)" (
    \t ->
      case t of
        PtlsTuple{} -> createLabeledTuple (tup t) (len t) (lisVersion t) s
        _ -> createException (createString (getLocation t) (show t ++ " is not a tuple"))
  )
getProperty "!getWrapObject" (PtlsLabel (PtlsLocated s loc)) =
  createBuiltIn loc "!getWrapObject(obj)" (
    \obj ->
      case obj of
        PtlsObject{} -> createLabeledObject (objValue obj) (showObj obj) s
        _ -> createException (createString (getLocation obj) (show obj ++ " is not an object"))
  )
getProperty "!getWrap" (PtlsLabel (PtlsLocated s loc)) =
  createBuiltIn loc "!getWrap(value)" (
    \val -> createLabeledTuple (toDyn val) 1 (createLocateable [val] loc) s
  )
getProperty "!getType" (PtlsLabel (PtlsLocated _ loc)) = createLabel loc "PtlsLabel"
getProperty "!getString" (PtlsLabel (PtlsLocated s loc)) = createString loc s
getProperty "!getSet" (PtlsLabel (PtlsLocated l loc)) = checkLabel (createLabel loc l) "Empty" (createSet loc [])
getProperty "!getRand" (PtlsLabel (PtlsLocated l loc)) = checkLabel (createLabel loc l) "IO" (createNumber loc (unsafePerformIO getRandom * 100))
getProperty "!getHead" (PtlsList (PtlsLocated l loc)) = if is_ptlsTrue(head l `ptlsEquals` createLabel loc "Empty") then createException (createString loc "Cannot get head of an empty list") else head l
getProperty "!getTail" (PtlsList (PtlsLocated l loc)) =
  let
    lis = createTerminatedList (createLocateable (tail l) loc)
    empty = createLabel loc "Empty"
  in
    if is_ptlsTrue (head (value (listValue lis)) `ptlsEquals` empty) then createLabel loc "Empty" else lis
getProperty "!getType" (PtlsList (PtlsLocated _ loc)) = createLabel loc "PtlsList"
getProperty "!getList" (PtlsList l) = createTerminatedList l
getProperty "!getAsin" (PtlsNumber (PtlsLocated n loc)) = createNumber loc (asin n)
getProperty "!getAcos" (PtlsNumber (PtlsLocated n loc)) = createNumber loc (acos n)
getProperty "!getAtan" (PtlsNumber (PtlsLocated n loc)) = createNumber loc (atan n)
getProperty "!getSin" (PtlsNumber (PtlsLocated n loc)) = createNumber loc (sin n)
getProperty "!getCos" (PtlsNumber (PtlsLocated n loc)) = createNumber loc (cos n)
getProperty "!getTan" (PtlsNumber (PtlsLocated n loc)) = createNumber loc (tan n)
getProperty "!getLn" (PtlsNumber (PtlsLocated n loc)) = createNumber loc (log n)
getProperty "!getString" (PtlsNumber (PtlsLocated n loc)) = createString loc (show n)
getProperty "!getType" (PtlsNumber (PtlsLocated n loc)) = createLabel loc "PtlsNumber"
getProperty "!getInt" (PtlsNumber (PtlsLocated n loc)) = createNumber loc (fromIntegral (round n))
getProperty "!getFloat" (PtlsNumber (PtlsLocated n loc)) = createNumber loc n
getProperty "!getAddElem" (PtlsSet s) =
  createBuiltIn (location s) "!getAddElem(elem)" (
    \e ->
      let
        (he, vs, loc) = (hash e, value s, location s)
      in
        if he `StrictMap.member` vs then internalCreateSet s else internalCreateSet (createLocateable (StrictMap.delete he vs) loc)
  )
getProperty "!getDelElem" (PtlsSet s) =
  createBuiltIn (location s) "!getAddElem(elem)" (
    \e ->
      let
        he = hash e
        vs = value s
        loc = location s
      in
        if not (he `StrictMap.member` vs) then internalCreateSet s else internalCreateSet (createLocateable (StrictMap.delete he vs) loc)
  )
getProperty "!getType" (PtlsSet (PtlsLocated _ loc)) = createLabel loc "PtlsSet"
getProperty "!getLength" (PtlsSet (PtlsLocated s loc)) = createNumber loc (fromIntegral (length (StrictMap.toList s)))
getProperty "!getList" (PtlsSet (PtlsLocated s loc)) = createList loc (map snd (StrictMap.toList s))
getProperty "!getUpper" (PtlsString (PtlsLocated s loc)) = createString loc (map toUpper s)
getProperty "!getLower" (PtlsString (PtlsLocated s loc)) = createString loc (map toLower s)
getProperty "!getInt" (PtlsString (PtlsLocated s loc)) = createNumber loc (read s)
getProperty "!getFloat" (PtlsString (PtlsLocated s loc)) = createNumber loc (read s)
getProperty "!getString" (PtlsString (PtlsLocated s loc)) = createString loc s
getProperty "!getList" (PtlsString (PtlsLocated s loc)) = createList loc (map (\x -> createString loc [x]) s)
getProperty "!getType" (PtlsString (PtlsLocated s loc)) = createLabel loc "PtlsString"
getProperty "!getLength" (PtlsString (PtlsLocated s loc)) = createNumber loc (fromIntegral (length s))
getProperty "!getLength" (PtlsTuple _ (PtlsLocated _ loc) _ ln) = createNumber loc (fromIntegral ln)
getProperty "!getList" (PtlsTuple _ (PtlsLocated ls loc) _ _) = createList loc ls
getProperty "!getType" (PtlsTuple _ (PtlsLocated _ loc) _ _) = createLabel loc "PtlsTuple"
getProperty "!getLabel" (PtlsTuple _ _ lb _) = lb
getProperty _ e@(PtlsException _) = e
getProperty o p = createException (createString (getLocation p) ("Can't get index " ++ show o ++ " from " ++ show p))

exceptZip loc a b = if length a /= length b then error (show (createException (createString loc ("Can't destructure this tuple of length " ++ show(length b) ++ " to " ++ show(length a) ++ " names"))))
                else zip a b

getRandom =
  do
   num <- randomIO :: IO Float
   return num

updateTupleList l k r f eq = filter (\(x, y) -> not (is_ptlsTrue (x`eq`f k))) l ++ [(f k, r)]

updateIndex :: Value -> Value -> Value -> Value
updateIndex _ _ e@(PtlsException _) = e
updateIndex _ e@(PtlsException _) _ = e
updateIndex e@(PtlsException _) _ _ = e
updateIndex (PtlsDict m l) (PtlsNumber (PtlsLocated k lock)) r =
  internalCreateDict (StrictMap.insert (hash (createNumber lock k)) r `drill` m) (updateTupleList l k r (createNumber lock) ptlsEquals)
updateIndex (PtlsDict m l) (PtlsString (PtlsLocated k lock)) r =
  internalCreateDict (StrictMap.insert (hash (createString lock k)) r `drill` m) (updateTupleList l k r (createString lock) ptlsEquals)
updateIndex (PtlsDict m l) (PtlsBool (PtlsLocated k lock)) r =
  internalCreateDict (StrictMap.insert (hash (createBool lock k)) r `drill` m) (updateTupleList l k r (createBool lock) ptlsEquals)
updateIndex (PtlsDict m l) (PtlsTuple tup (PtlsLocated lis lock) (PtlsLabel (PtlsLocated lab _)) len) r =
  internalCreateDict (StrictMap.insert (hash (createLabeledTuple tup len located lab)) r `drill` m) (updateTupleList l lab r (createLabeledTuple tup len located) ptlsEquals) where
    located = createLocateable lis lock
updateIndex (PtlsArray arr) (PtlsNumber (PtlsLocated n locn)) r =
  case value arr Vector.!? round n of
    Just _ -> internalCreateArray ((Vector.// [(round n, r)]) `drill` arr)
    Nothing -> createException (createString (location arr) ("Can't get index " ++ show n ++ " from " ++ show (value arr)))
updateIndex k d _ = createException (createString (getLocation k) ("Can't change index " ++ show d ++ " of " ++ show k))

updateField :: Value -> String -> Value -> Value
updateField _ _ e@(PtlsException _) = e
updateField e@(PtlsException _) _ _ = e
updateField (PtlsObject o so ol) k r =
  internalCreateObject (StrictMap.insert (hash k) r `drill` o) (updateTupleList so k r id (\a b -> createBool (location o) (a == b))) ol
updateField p d _ = createException (createString (getLocation p) ("Can't change index " ++ show d ++ " of " ++ show p))

tempLoc = PtlsLocation{ln = 1, cn = 2, fn = "p.js"}
