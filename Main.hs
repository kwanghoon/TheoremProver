
module Main where

{- Term and Forumula -}
data Term = 
   Var String
 | Param String [String]
 | Bound Int
 | Fun String [Term]
 deriving (Show,Eq)

data Form =
   Pred String [Term]
 | Conn String [Form]
 | Quant String String Form
 deriving (Show,Eq)

prec_of "~" = 4
prec_of "&" = 3
prec_of "|" = 2
prec_of "<->" = 1
prec_of "-->" = 0
prec_of _ = -1

replace u1 u2 t =
   if t==u1 then u2 else
   case t of 
     Fun a ts -> Fun a (map (replace u1 u2) ts)
     _ -> t;

abstract i t (Pred a ts) = 
   Pred a (map (replace t (Bound i)) ts)
abstract i t (Conn b ps) =
   Conn b (map (abstract i t) ps)
abstract i t (Quant qnt b p) =
   Quant qnt b (abstract (i+1) t p)

subst i t (Pred a ts) =
   Pred a (map (replace (Bound i) t) ts)
subst i t (Conn b ps) =
   Conn b (map (subst i t) ps)
subst i t (Quant qnt b p) =
   Quant qnt b (subst (i+1) t p)

accumform f (Pred _ ts) xs = foldr f xs ts 
accumform f (Conn _ ps) xs = foldr (accumform f) xs ps 
accumform f (Quant _ _ p) xs = accumform f p xs

accumgoal f ps qs xs = foldr f (foldr f xs qs) ps

termvars (Var a) bs = 
   if a `elem` bs then bs else a : bs
termvars (Fun _ ts) bs = foldr termvars bs ts
termvars (_) bs = bs

goalvars = accumgoal (accumform termvars)

termparams (Param a bs) pairs = 
   if (a,bs) `elem` pairs then pairs 
   else (a,bs) : pairs
termparams (Fun _ ts) pairs = 
   foldr termparams pairs ts
termparams (_) pairs = pairs

goalparams = accumgoal (accumform termparams)

{- Keyword -}

alphas = ["ALL", "EX"] ++ tactics_keywords
symbols = ["~", "&", "|", ".", ",", "?", 
           "(", ")", "<->", "-->", "|-"]

{- Lexer -}

data Token =
   Key String
 | Id String
 deriving Show

scan s toks = 
   if s == "" then toks
   else
     let [(tok,s')] = lex s in
     if tok `elem` alphas || tok `elem` symbols
     then scan s' (toks ++ [Key tok])
     else scan s' (toks ++ [Id tok])

{- Parser -}

type Parser a = [Token] -> Maybe (a,[Token])

keywd a (Key b : toks) = 
   if a==b then Just (a,toks)
   else Nothing
keywd a toks = Nothing

ident (Id a : toks) = Just (a,toks)
ident _ = Nothing

numb (Id a : toks) = 
   if and (map (\x->x `elem` ['0'..'9']) a) 
   then Just (read a,toks)
   else Nothing
numb _ = Nothing

modi ph f toks = 
   case ph toks of
     Just (x,toks2) -> Just (f x, toks2)
     Nothing -> Nothing

alt ph1 ph2 toks =
   case ph1 toks of
     Nothing -> ph2 toks
     Just x -> Just x

sequ ph1 ph2 toks =
   case ph1 toks of
     Just (x,toks2) -> 
       case ph2 toks2 of
         Just (y,toks3) -> Just ((x,y),toks3)
         Nothing -> Nothing
     Nothing -> Nothing

empty toks = Just ([], toks)

rep ph toks =  
   alt (modi (sequ ph (rep ph)) (uncurry (:)))
   empty toks

infixes ph prec_of apply = over 0
   where
      over k toks = next k (ph toks)
      next k (Just (x, Key a : toks)) = 
         if prec_of a < k then Just (x, Key a : toks)
         else next k (modi (over (prec_of a)) (apply a x) toks)
      next k (Just (x, toks)) = Just (x, toks)
      next k Nothing = Nothing

reader ph a = 
   case ph (scan a []) of
     Just (x, []) -> Just x
     _ -> Nothing

applyP pf pa toks =
   case pf toks of
      Nothing -> Nothing
      Just (f,toks) -> 
         case pa toks of
            Nothing -> Nothing
            Just (a,toks) -> Just (f a, toks)

{- Grammar fo terms and formular -}

list ph = modi 
   (sequ ph (rep (modi (sequ (keywd ",") ph) snd))) 
   (uncurry (:))

pack ph = alt
   (modi
       (sequ (sequ (keywd "(") (list ph)) (keywd ")"))
       (snd . fst))
   empty

term = alt
   (modi (sequ ident (pack term)) (uncurry Fun))
   (modi (sequ (keywd "?") ident) (Var . snd))

makeQuant (((qnt,b),_),p) =
   Quant qnt b (abstract 0 (Fun b []) p)

makeConn a p q = Conn a [p,q]

makeNeg (_,p) = Conn "~" [p]

form = alt
   (modi
      (sequ (sequ (sequ (keywd "ALL") ident) 
      (keywd ".")) form) makeQuant)
   (alt
      (modi
         (sequ (sequ (sequ (keywd "EX") ident)
         (keywd ".")) form)
         makeQuant)
      (infixes primary prec_of makeConn))

primary = alt
   (modi (sequ (keywd "~") primary) makeNeg)
   (alt
       (modi 
          (sequ (sequ (keywd "(") form) 
          (keywd ")"))
          (snd . fst))
       (modi
          (sequ ident (pack term))
          (uncurry Pred)))

readForm = reader form 

{- Pretty -}

data T = 
   Block [T] Int Int
 | String String
 | Break Int

breakdist (Block _ _ len:es) after = len + breakdist es after
breakdist (String s:es) after = length s + breakdist es after
breakdist (Break _:es) after = 0
breakdist [] after = after

len (Block _ _ n) = n
len (String s) = length s
len (Break n) = n

str = String
brk = Break

blo indent es =
   Block es indent (sum es 0)
   where
      sum [] k = k
      sum (e:es) k = sum es (len e + k)

ppr e margin = 
   let (space,s) = printing [e] margin 0 margin ""
       (space',s') = newline space s
   in s'
   where
      blanks 0 space s = (space, s)
      blanks n space s = blanks (n-1) (space-1) (s++" ")

      newline space s = (margin, s++"\n")

      printing [] _ _ space s = (space,s)
      printing (e:es) blockspace after space s =
         let (space',s') = onestep e es blockspace after space s
         in  printing es blockspace after space' s'

      onestep e es blockspace after space s =
         case e of
             Block bes indent len -> 
                printing bes (space-indent) (breakdist es after) space s
             String str -> (space-length str, s++str)
             Break n -> 
                if n+breakdist es after <= space
                then blanks n space s
                else 
                   let (space',s') = newline space s in
                      blanks (margin-blockspace) space' s'

{- Printer -}

enclose sexp = blo 1 [str "(", sexp, str ")"]

commas [] = []
commas (sexp:sexps) = str "," : brk 1 : sexp : commas sexps

_list (sexp:sexps) = blo 0 (sexp : commas sexps)

_term (Param a _) = str a
_term (Var a) = str ("?" ++ a)
_term (Bound i) = str "??UNMATCHED INDEX??"
_term (Fun a ts) = blo 0 [str a, args ts]

args [] = str ""
args ts = enclose (_list (map _term ts))

_form k (Pred a ts) = blo 0 [str a, args ts]
_form k (Conn "~" [p]) = blo 0 [str "~", _form (prec_of "~") p]
_form k (Conn c [p,q]) =
   let pf = _form (maxl [prec_of c, k])
       sexp = blo 0 [pf p, str (" "++c), brk 1, pf q]
   in  if prec_of c <= k then enclose sexp else sexp
_form k (Quant qnt b p) =
   let q = subst 0 (Fun b []) p
       sexp = blo 2 [str (qnt++" "++b++"."), brk 1, _form 0 q]
   in  if k>0 then enclose sexp else sexp
_form k _ = str "??UNKNOWN FORMULA??"

formlist [] = str "empty"
formlist ps = _list (map (_form 0) ps)

pr_form p = ppr (_form 0 p) 80

pr_goal n (ps,qs) =
   ppr (blo 4 [str (" "++makestring n++". "),
             formlist ps, brk 2, str "|- ", formlist qs]) 50

{- Unification  -}

unifylists env = unifyl
   where
      chase (Var a) = 
         case lookup a env of
            Just x -> x
            Nothing -> Var a
      chase t = t

      occurs a (Fun _ ts) = occsl a ts
      occurs a (Param _ bs) = occsl a (map Var bs)
      occurs a (Var b) = a==b || 
         case lookup b env of 
            Just x -> occurs a x
            Nothing -> False
      occurs a _ = False

      occsl a = exists (occurs a)

      unify (Var a) t = 
         if t==Var a then Just env 
         else if occurs a t then Nothing 
         else Just ((a,t):env)
      unify t (Var a) = unify (Var a) t
      unify (Param a _) (Param b _) = 
         if a==b then Just env else Nothing
      unify (Fun a ts) (Fun b us) = 
         if a==b then unifyl ts us else Nothing
      unify _ _ = Nothing

      unifyl [] [] = Just env
      unifyl (t:ts) (u:us) = 
         case unify (chase t) (chase u) of
            Just x -> unifylists x ts us
            Nothing -> Nothing
      unifyl _ _ = Nothing

atoms (Pred a ts) (Pred b us) = 
   if a==b then unifylists [] ts us else Nothing
atoms _ _ = Nothing

instterm env (Fun a ts) = Fun a (map (instterm env) ts)
instterm env (Param a bs) = 
   Param a (foldr termvars [] (map (instterm env . Var) bs))
instterm env (Var a) = 
   case lookup a env of
      Just x -> instterm env x
      Nothing -> Var a
instterm env t = t

instform env (Pred a ts) = Pred a (map (instterm env) ts)
instform env (Conn b ps) = Conn b (map (instform env) ps)
instform env (Quant qnt b p) = Quant qnt b (instform env p)

instgoal env (ps,qs) = 
   (map (instform env) ps, map (instform env) qs)

{- Proof -}

data State = State [Goal] Form Int deriving Show

type Goal = ([Form],[Form])

maingoal (State gs p _) = p
subgoals (State gs p _) = gs

initial p = State [([],[p])] p 0

final (State [] _ _) = True
final (_) = False

splicegoals gs newgs i = take (i-1) gs ++ newgs ++ drop i gs

basic_tac = _SUBGOAL (\(ps,qs) ->
   case any id [p == q | p <- ps, q <- qs] of
     True  -> Just []
     False -> Nothing)

unifiable [] _ = []
unifiable (p:ps) qs = find qs
   where
      find [] = unifiable ps qs
      find (q:qs) = 
         case atoms p q of
            Just x -> x : find qs
            Nothing -> find qs

atomic (Pred _ _) = True
atomic (_) = False

inst [] st = st
inst env (State gs p n) = 
   State (map (instgoal env) gs) (instform env p) n

unify_tac i (State gs p n) =
   case nth gs (i-1) of
      Nothing -> []
      Just (ps,qs) -> 
         let next env = inst env 
                (State (splicegoals gs [] i) p n)
         in  (map next (unifiable (filter atomic ps) 
                                  (filter atomic qs)))

splitconn a qs = 
   case get qs of
      Nothing -> Nothing
      Just x -> Just (x, del qs)
   where
      get [] = Nothing
      get (Conn b ps : qs) = if a==b then Just ps 
                             else get qs
      get (q:qs) = get qs

      del [] = []
      del (q@(Conn b _):qs) = if a==b then qs 
                              else q:del qs
      del (q:qs) = q : del qs

-- propRule in the book
_SUBGOAL goalf i (State gs p n) = 
   case nth gs (i-1) of
      Nothing -> []
      Just x -> 
         case goalf x of
            Nothing -> []
            Just z ->
               let gs2 = splicegoals gs z i 
               in [State gs2 p n]

conj_left_tac = _SUBGOAL (\(ps,qs) ->
   case splitconn "&" ps of
      Nothing -> Nothing
      Just ([p1,p2],ps') -> Just [(p1:p2:ps',qs)])

conj_right_tac = _SUBGOAL (\(ps,qs) ->
   case splitconn "&" qs of
      Nothing -> Nothing
      Just ([q1,q2],qs') -> Just [(ps,q1:qs'),(ps,q2:qs')])

disj_left_tac = _SUBGOAL (\(ps,qs) ->
   case splitconn "|" ps of
      Nothing -> Nothing
      Just ([p1,p2],ps') -> Just [(p1:ps',qs),(p2:ps',qs)])

disj_right_tac = _SUBGOAL (\(ps,qs) ->
   case splitconn "|" qs of
      Nothing -> Nothing
      Just ([q1,q2],qs') -> Just [(ps,q1:q2:qs')])

imp_left_tac = _SUBGOAL (\(ps,qs) ->
   case splitconn "-->" ps of
      Nothing -> Nothing
      Just ([p1,p2],ps') -> Just [(ps',p1:qs),(p2:ps',qs)])

imp_right_tac = _SUBGOAL (\(ps,qs) ->
   case splitconn "-->" qs of
      Nothing -> Nothing
      Just ([q1,q2],qs') -> Just [(q1:ps,q2:qs')])

neg_left_tac = _SUBGOAL (\(ps,qs) ->
   case splitconn "~" ps of
      Nothing -> Nothing
      Just ([p1],ps') -> Just [(ps',p1:qs)])

neg_right_tac = _SUBGOAL (\(ps,qs) ->
   case splitconn "~" qs of
      Nothing -> Nothing
      Just ([q1],qs') -> Just [(q1:ps,qs')])

iff_left_tac = _SUBGOAL (\(ps,qs) ->
   case splitconn "<->" ps of
      Nothing -> Nothing
      Just ([p1,p2],ps') -> Just [(p1:p2:ps',qs),(ps',p1:p2:qs)])

iff_right_tac = _SUBGOAL (\(ps,qs) ->
   case splitconn "<->" qs of
      Nothing -> Nothing
      Just ([q1,q2],qs') -> Just [(q1:ps,q2:qs'),(q2:ps,q1:qs')])

splitquant qnt qs = 
   case get qs of
      Nothing -> Nothing
      Just x -> Just (x,del qs)
   where
      get [] = Nothing
      get ((q@(Quant qnt2 _ p)):qs) =
         if qnt==qnt2 then Just q else get qs
      get (q:qs) = get qs

      del [] = []
      del ((q@(Quant qnt2 _ p)):qs) =
         if qnt==qnt2 then qs else q:del qs
      del (q:qs) = q : del qs

letter n = [head (drop n ['a'..])]

gensym n =
   if n<26 then "_" ++ letter n
   else gensym (n `div` 26) ++ letter (n `mod` 26)

_SUBGOAL_SYM goalf i (State gs p n) =
   case nth gs (i-1) of
      Nothing -> []
      Just x ->
         case goalf (x,gensym n) of
            Nothing -> []
            Just y -> 
               let gs2 = splicegoals gs y i
               in [State gs2 p (n+1)]

all_left_tac = _SUBGOAL_SYM (\((ps,qs),b)->
   case splitquant "ALL" ps of
      Nothing -> Nothing
      Just (qntform@(Quant _ _ p),ps') ->
         let px = subst 0 (Var b) p
         in  Just [(px:ps'++[qntform],qs)])

all_right_tac = _SUBGOAL_SYM (\((ps,qs),b)->
   case splitquant "ALL" qs of
      Nothing -> Nothing
      Just (Quant _ _ q,qs') ->
         let vars = goalvars ps qs [] 
             qx = subst 0 (Param b vars) q
         in Just [(ps,qx:qs')])

ex_left_tac = _SUBGOAL_SYM (\((ps,qs),b)->
   case splitquant "EX" ps of
      Nothing -> Nothing
      Just (Quant _ _ p,ps') ->
         let vars = goalvars ps qs []
             px = subst 0 (Param b vars) p
         in  Just [(px:ps',qs)])

ex_right_tac = _SUBGOAL_SYM (\((ps,qs),b)->
   case splitquant "EX" qs of
      Nothing -> Nothing
      Just (qntform@(Quant _ _ q),qs') ->
         let qx = subst 0 (Var b) q
         in Just [(ps,qx:qs'++[qntform])])

{- (Manual) Tacticals -}

type Tactical = State -> [State]

_THEN tac1 tac2 st = concat (map tac2 (tac1 st))

_ORELSE :: Tactical -> Tactical -> Tactical
_ORELSE tac1 tac2 st = 
   let st1 = tac1 st in
   if null st1 then tac2 st else st1

_APPEND tac1 tac2 st = concat [tac1 st, tac2 st]

all_tac st = [st]

no_tac st = []

_TRY :: Tactical -> Tactical
_TRY tac = _ORELSE tac all_tac

_REPEAT tac = _ORELSE (_THEN tac (_REPEAT tac)) all_tac

_DEPTH_FIRST pred tac st = 
   if pred st then all_tac st
   else _THEN tac (_DEPTH_FIRST pred tac) st

_ORI f1 f2 i = _ORELSE (f1 i) (f2 i)

{- (Automatic) Tacticals -}

safe_step_tac = 
   conj_left_tac `_ORI` disj_right_tac `_ORI` imp_right_tac `_ORI`
   neg_left_tac `_ORI` neg_right_tac `_ORI`
   ex_left_tac `_ORI` all_right_tac `_ORI`
   conj_right_tac `_ORI` disj_left_tac `_ORI` imp_left_tac `_ORI`
   iff_left_tac `_ORI` iff_right_tac

quant_tac i =
   _TRY (all_left_tac i) `_THEN` (_TRY (ex_right_tac i))

step_tac = unify_tac `_ORI` safe_step_tac `_ORI` quant_tac

depth_tac = _DEPTH_FIRST final (step_tac 1)

{- Utility -}

maxl [m] = m
maxl (m:n:ns) = 
   if m>n then maxl (m:ns) 
   else maxl (n:ns)

makestring :: Int -> String
makestring n = show n

exists f xs = or (map f xs)

nth (x:_) 0 = Just x
nth (x:xs) n = 
   if n>0 then nth xs (n-1)
   else Nothing
nth _ _ = Nothing

{- Command Line -}

question s = " ?" ++ s

printpar (a,[]) = return ()
printpar (a,ts) =
   putStr (a ++ " not in " ++ 
          concat (map question ts) ++ "\n")

printgoals _ [] = return ()
printgoals n (g:gs) = 
   do { putStr (pr_goal n g)
      ; printgoals (n+1) gs
      }

pr st = 
   let p = maingoal st 
       gs = subgoals st
   in 
   do { putStr (pr_form p)
      ; if final st
        then putStr ("No subgoals left!\n")
        else do { printgoals 1 gs 
                ; mapM_ printpar (foldr (uncurry goalparams) [] gs)
                }
      }

initstate = initial (Pred "No goal yet!" [])

goal curr_state arg =
   case readForm arg of
      Nothing -> 
        do { putStrLn "*** error in parsing formula ***"
           ; return curr_state
           }
      Just x -> 
        do { let curr_state = initial x
           ; pr curr_state
           ; return curr_state
           }

by curr_state tac = 
    case tac curr_state of
       [] -> do { putStrLn "*** Tactic FAILED ***"
                ; return curr_state
                }
       (s:_) -> do { let curr_state = s
                   ; pr curr_state
                   ; return curr_state
                   }


main = 
   do { putStrLn "Starting Tactical Theorem Prover..."
      ; loop initstate
      ; putStrLn "end..." 
      }

loop curr_state =
   do { doPrompt
      ; cmdstr <- getLine
      ; let [(cmd,arg)] = lex cmdstr
      ; case cmd of 
           "goal" -> do {s'<-doGoal curr_state arg; loop s'}
           "by" -> do {s'<-doBy curr_state arg; loop s'}
           "pr" -> do {doPr curr_state; loop curr_state }
           "quit" -> return ()
           "" -> loop curr_state
           _ -> do {doUnknownCmd; loop curr_state}
      }

doGoal curr_state arg = goal curr_state arg

doBy curr_state arg = 
   case reader tactical arg of
      Nothing -> do { putStrLn "*** command error ***"
                    ; return curr_state
                    }
      Just tac -> by curr_state tac

doPr curr_state =
   do { pr curr_state
      ; return curr_state
      }

doPrompt = putStr "> "

doUnknownCmd = putStrLn "Sorry?"

{- tactical parser -}

tactics_keywords = [
   {- tacticals -}
   "TRY", "REPEAT", "DEPTH_FIRST",
   "--", "||", "|@|", "ORI", "all", "no",
   {- tactics -}
   "basic",
   "unify", "conjL", "conjR", "disjL", "disjR", 
   "impL", "impR", "negL", "negR", "iffL", "iffR",
   "allL", "allR", "exL", "exR", 
   {- automatic tacticals -}
   "safe_step", "quant", "step", "depth"
   ]

tactical = 
    alt (modi (sequ (keywd "TRY") tactical) 
              (\(_,tac) -> _TRY tac))
   (alt (modi (sequ (keywd "REPEAT") tactical) 
              (\(_,tac) -> _REPEAT tac))
   (alt (modi (sequ (keywd "DEPTH_FIRST") tactical) 
              (\(_,tac) -> _DEPTH_FIRST final tac))
        (infixes tactic _prec_of makeTactical)))

tactic = alt (modi (sequ (sequ (keywd "(") tactical) (keywd ")")) 
                   (snd . fst))
   (alt (modi (keywd "all") (\_ -> all_tac))
   (alt (modi (keywd "no") (\_ -> no_tac))
   (alt (modi (sequ (keywd "safe_step") numb) (\ (x,n)->safe_step_tac n))
   (alt (modi (sequ (keywd "quant") numb) (\ (x,n)->quant_tac n))
   (alt (modi (sequ (keywd "step") numb) (\ (x,n)->step_tac n))
   (alt (modi (keywd "depth") (\ (x)->depth_tac))
   (alt (modi (sequ (keywd "basic") numb) (\ (x,n)->basic_tac n))
   (alt (modi (sequ (keywd "unify") numb) (\ (x,n)->unify_tac n))
   (alt (modi (sequ (keywd "conjL") numb) (\ (x,n)->conj_left_tac n))
   (alt (modi (sequ (keywd "conjR") numb) (\ (x,n)->conj_right_tac n))
   (alt (modi (sequ (keywd "disjL") numb) (\ (x,n)->disj_left_tac n))
   (alt (modi (sequ (keywd "disjR") numb) (\ (x,n)->disj_right_tac n))
   (alt (modi (sequ (keywd "impL") numb) (\ (x,n)->imp_left_tac n))
   (alt (modi (sequ (keywd "impR") numb) (\ (x,n)->imp_right_tac n))
   (alt (modi (sequ (keywd "negL") numb) (\ (x,n)->neg_left_tac n))
   (alt (modi (sequ (keywd "negR") numb) (\ (x,n)->neg_right_tac n))
   (alt (modi (sequ (keywd "iffL") numb) (\ (x,n)->iff_left_tac n))
   (alt (modi (sequ (keywd "iffR") numb) (\ (x,n)->iff_right_tac n))
   (alt (modi (sequ (keywd "allL") numb) (\ (x,n)->all_left_tac n))
   (alt (modi (sequ (keywd "allR") numb) (\ (x,n)->all_right_tac n))
   (alt (modi (sequ (keywd "exL") numb) (\ (x,n)->ex_left_tac n))
        (modi (sequ (keywd "exR") numb) (\ (x,n)-> ex_right_tac n))
   )))))))))))))))))))))

_prec_of "--" = 5
_prec_of "||" = 0
_prec_of "|@|" = 0
-- _prec_of "ORI" = 0
_prec_of _ = -1

makeTactical :: String -> Tactical -> Tactical -> Tactical
makeTactical "--" tac1 tac2 = _THEN tac1 tac2
makeTactical "||" tac1 tac2 = _ORELSE tac1 tac2
makeTactical "|@|" tac1 tac2 = _APPEND tac1 tac2
-- makeTactical "ORI" tac1 tac2 = \n -> _ORI tac1 tac2 n
makeTactical _ tac1 tac2 = error "*** fatal error ***"
