module ProofVerifier where

import qualified System.Environment as Env
import qualified Data.Map as Map

type Label = String
type LHSLabel = Label
type RHSLabel = Label
type InputLabel = Label
type ImplyLabel = Label

data Statement
  = MkContradiction
  | MkPrimitive Label
  | MkNot Statement
  | MkAnd Statement Statement
  | MkOr Statement Statement
  | MkImplies Statement Statement
  deriving(Eq, Read)

instance Show Statement where
  show MkContradiction 
    = "⊥"
  show (MkPrimitive label) 
    = label
  show (MkNot stmt)
    = "(not " ++ show stmt ++ ")"
  show (MkAnd lhs rhs)
    = "(" ++ show lhs ++ " and " ++ show rhs ++ ")"
  show (MkOr lhs rhs)
    = "(" ++ show lhs ++ " or " ++ show rhs ++ ")"
  show (MkImplies lhs rhs)
    = "(" ++ show lhs ++ " implies " ++ show rhs ++ ")"

data Tactic
  = MkDirect Label
  | MkShowingAnd LHSLabel RHSLabel
  | MkShowingOr Label
  | MkShowingNot Label Context
  | MkShowingImplies Label Context
  | MkShowingContradiction LHSLabel RHSLabel
  | MkUsingAnd Label
  | MkUsingOr Label LHSLabel RHSLabel Context Context
  | MkUsingImplies InputLabel ImplyLabel
  | MkUsingContradiction Label
  | MkExcludedMiddle
  | MkTakeForGranted
  deriving(Eq, Read, Show)

data Context
  = MkLetIn Label Statement Tactic Context
  | MkRet Statement Tactic
  deriving(Eq, Read, Show)

type LHSStatement = Statement
type RHSStatement = Statement
type ExpectedStatement = Statement
type ActualStatement = Statement
type ShadowedStatement = Statement
type NewStatement = Statement

data TacticError
  = MkStatementNotFound Label
  | MkNotAnd ActualStatement
  | MkLeftShowAndBranchMismatch LHSStatement RHSStatement ActualStatement
  | MkRightShowAndBranchMismatch LHSStatement RHSStatement ActualStatement
  | MkNotOr ActualStatement
  | MkShowOrBranchMismatch LHSStatement RHSStatement ActualStatement
  | MkShowNotContextError ContextError
  | MkShowImpliesContextError ContextError
  | MkUseAndBranchMismatch LHSStatement RHSStatement ActualStatement
  | MkUseOrLHSContextError ContextError
  | MkUseOrRHSContextError ContextError
  | MkNoContradiction LHSStatement RHSStatement
  | MkNotAContradiction ActualStatement
  | MkNotExcludedMiddle ActualStatement
  | MkNotImplies ActualStatement
  | MkImpliesInputMismatch Statement Statement ActualStatement 
  | MkImpliesOutputMismatch Statement Statement ActualStatement
  | MkNotNot ActualStatement
  | MkDirectProofMismatch ExpectedStatement ActualStatement
  deriving(Eq, Read)

instance Show TacticError where
  show (MkStatementNotFound l) 
    = "undefined label \"" ++ l ++ "\""
  show (MkNotAnd stmt)
    = "expected and statement, got \"" ++ show stmt ++ "\""
  show (MkLeftShowAndBranchMismatch lhs rhs actual)
    = "statement \"" ++ show actual 
    ++ "\" does not match LHS of and statement \"" 
    ++ show (MkAnd lhs rhs) ++ "\""
  show (MkRightShowAndBranchMismatch lhs rhs actual)
    = "statement \"" ++ show actual 
    ++ "\" does not match RHS of and statement \"" 
    ++ show (MkAnd lhs rhs) ++ "\""
  show (MkNotOr stmt)
    = "expected or statement, got \"" ++ show stmt ++ "\""
  show (MkShowOrBranchMismatch lhs rhs actual)
    = "statement \"" ++ show actual
    ++ "\" does not match LHS or RHS of or statement \""
    ++ show (MkOr lhs rhs) ++ "\""
  show (MkShowNotContextError e)
    = "in the nested context block for \"Showing not\" tactic\n" ++ show e
  show (MkShowImpliesContextError e)
    = "in the nested context block for \"Showing not\" tactic\n" ++ show e
  show (MkUseAndBranchMismatch lhs rhs actual)
    = "can't infer statement \"" ++ show actual 
    ++ "\" from and statement " ++ show (MkAnd lhs rhs) ++ "\""
  show (MkUseOrLHSContextError e)
    = "in the nested LHS context block for \"Using or\" tactic\n" ++ show e
  show (MkUseOrRHSContextError e)
    = "in the nested RHS context block for \"Using or\" tactic\n" ++ show e
  show (MkNoContradiction lhs rhs)
    = "statements \"" ++ show lhs ++ "\" and \"" ++ show rhs 
    ++ "\" do not directly contradict with each other"
  show (MkNotAContradiction stmt)
    = "expected contradiction, got \"" ++ show stmt ++ "\""
  show (MkNotExcludedMiddle stmt)
    = "statement \"" ++ show stmt 
    ++ "\" can not be directly derived from the law of excluded middle"
  show (MkNotImplies actual)
    = "expected implies statement, got \"" ++ show actual ++ "\""
  show (MkImpliesInputMismatch p q actual)
    = "can't accept \"" ++ show actual 
    ++ "\" as an input for implies statement \""
    ++ show (MkImplies p q) ++ "\""
  show (MkImpliesOutputMismatch p q actual)
    = "can't derive \"" ++ show actual 
    ++ "\" from implies statement \""
    ++ show (MkImplies p q) ++ "\""
  show (MkNotNot stmt)
    = "expected not statement, got \"" ++ show stmt ++ "\""
  show (MkDirectProofMismatch p q)
    = "can't prove \"" ++ show q ++ "\" from \"" ++ show p 
    ++ "\" directly as p and q are not equivalent"

data ContextError
  = MkLetInError Label TacticError
  | MkRetError TacticError
  | MkShadowing Label ShadowedStatement NewStatement
  | MkInvalidGoalReached ExpectedStatement ActualStatement
  deriving(Eq, Read)

instance Show ContextError where
  show (MkLetInError l e)
    = "error in label assignment for " ++ show l ++ ": " ++ show e
  show (MkRetError e)
    = "error in final proof step: " ++ show e
  show (MkShadowing l olds news)
    = "shadowing error: attempt to redefine label" ++ show l
    ++ "\nshadowed assignment: \"" ++ show olds 
    ++ "\"\nnew assignment: \"" ++ show news ++ "\""
  show (MkInvalidGoalReached exp act)
    = "error in final proof step: invalid goal reached\n"
    ++ "\nexpected final statement (goal): \"" ++ show exp ++ "\""
    ++ "\nactual final statement: \"" ++ show act ++ "\""

type TacticResult = Either TacticError
type ContextResult = Either ContextError

fromLetInTacticResult :: Label -> TacticResult a -> ContextResult a
fromLetInTacticResult l (Left e)
  = Left $ MkLetInError l e
fromLetInTacticResult l (Right val)
  = Right val

fromReturnTacticResult :: TacticResult a -> ContextResult a
fromReturnTacticResult (Left e)
  = Left $ MkRetError e
fromReturnTacticResult (Right val)
  = Right val

fromContextResult :: (ContextError -> TacticError) -> ContextResult a -> TacticResult a
fromContextResult pred (Left e)
  = Left $ pred e
fromContextResult pred (Right val)
  = Right val

type ContextStatements = Map.Map Label Statement
type StatementsUniverse = [ContextStatements]

lookUpStatement :: StatementsUniverse -> Label -> TacticResult Statement
lookUpStatement [] l
  = Left $ MkStatementNotFound l
lookUpStatement (u:us) l
  = case Map.lookup l u of
      Nothing -> lookUpStatement us l
      Just s -> Right s

addScope :: StatementsUniverse -> StatementsUniverse
addScope = ((Map.empty :: ContextStatements):)

addStatement :: StatementsUniverse -> Statement -> Label -> StatementsUniverse
addStatement [] s l
  = addStatement (addScope []) s l
addStatement (u:us) s l
  = Map.insert l s u:us

verifyShowAndBranches :: Statement -> Statement -> Statement -> TacticResult ()
verifyShowAndBranches stmt@(MkAnd lhs rhs) left right
  | lhs /= left  = Left $ MkLeftShowAndBranchMismatch lhs rhs left
  | rhs /= right = Left $ MkRightShowAndBranchMismatch lhs rhs right
  | otherwise    = Right ()
verifyShowAndBranches stmt _ _
  = Left $ MkNotOr stmt

verifyShowingAnd
  :: StatementsUniverse 
  -> Label 
  -> Label 
  -> Statement 
  -> TacticResult ()
verifyShowingAnd u ll lr goal
  = do
      lhs <- lookUpStatement u ll
      rhs <- lookUpStatement u lr
      verifyShowAndBranches goal lhs rhs
      return ()

verifyShowOrBranches :: Statement -> Statement -> TacticResult ()
verifyShowOrBranches stmt@(MkOr lhs rhs) base
  | lhs == base = Right ()
  | rhs == base = Right ()
  | otherwise   = Left $ MkShowOrBranchMismatch lhs rhs base
verifyShowOrBranches stmt _
  = Left $ MkNotOr stmt

verifyShowingOr
  :: StatementsUniverse 
  -> Label
  -> Statement 
  -> TacticResult ()
verifyShowingOr u lbase goal
  = do
      base <- lookUpStatement u lbase
      verifyShowOrBranches goal base
      return ()

verifyShowingNot
  :: StatementsUniverse
  -> Label
  -> Context
  -> Statement
  -> TacticResult ()
verifyShowingNot u la ctx (MkNot s)
  = fromContextResult MkShowNotContextError $ do
      let u' = addStatement (addScope u) s la
      verifyContext u' MkContradiction ctx
verifyShowingNot _ _ _ s
  = Left $ MkNotNot s

verifyShowingImplies
  :: StatementsUniverse
  -> Label
  -> Context
  -> Statement
  -> TacticResult ()
verifyShowingImplies u la ctx (MkImplies i o)
  = fromContextResult MkShowImpliesContextError $ do
      let u' = addStatement (addScope u) i la
      verifyContext u' o ctx
verifyShowingImplies _ _ _ s
  = Left $ MkNotImplies s

checkContradiction :: Statement -> Statement -> TacticResult ()
checkContradiction lhs@(MkNot erhs) arhs
  | erhs == arhs = Right ()
checkContradiction alhs rhs@(MkNot elhs)
  | elhs == alhs = Right ()
checkContradiction lhs rhs
  = Left $ MkNoContradiction lhs rhs

verifyShowingContradiction
  :: StatementsUniverse
  -> Label
  -> Label
  -> Statement
  -> TacticResult ()
verifyShowingContradiction u ll rl MkContradiction
  = do
      lhs <- lookUpStatement u ll
      rhs <- lookUpStatement u rl
      checkContradiction lhs rhs
verifyShowingContradiction _ _ _ s
  = Left $ MkNotAContradiction s

verifyUseAndBranches :: Statement -> Statement -> TacticResult ()
verifyUseAndBranches stmt@(MkAnd lhs rhs) goal
  | lhs == goal = Right ()
  | rhs == goal = Right ()
  | otherwise   = Left $ MkUseAndBranchMismatch lhs rhs goal
verifyUseAndBranches stmt _
  = Left $ MkNotAnd stmt

verifyUsingAnd
  :: StatementsUniverse
  -> Label
  -> Statement
  -> TacticResult ()
verifyUsingAnd u lbase goal
  = do
      base <- lookUpStatement u lbase
      verifyUseAndBranches base goal
      return ()

verifyUsingOr
  :: StatementsUniverse
  -> Label
  -> LHSLabel
  -> RHSLabel
  -> Context
  -> Context
  -> Statement
  -> TacticResult ()
verifyUsingOr u lbase lla lra lctx rctx goal
  = case lookUpStatement u lbase of
      Right (MkOr lhs rhs) -> 
        do
          let lu = addStatement (addScope u) lhs lla
          let ru = addStatement (addScope u) rhs lra
          fromContextResult MkUseOrLHSContextError $ verifyContext lu goal lctx
          fromContextResult MkUseOrRHSContextError $ verifyContext ru goal rctx
      Right s -> Left $ MkNotOr s
      Left e -> Left e


verifyUsingImplies
  :: StatementsUniverse
  -> InputLabel
  -> ImplyLabel
  -> Statement
  -> TacticResult ()
verifyUsingImplies u lin lim s
  = do
      input <- lookUpStatement u lin
      impl <- lookUpStatement u lim
      case impl of
        MkImplies p q -> 
          if input /= p 
            then Left $ MkImpliesInputMismatch p q input 
            else 
              if q /= s 
                then Left $ MkImpliesOutputMismatch p q s 
                else Right ()
        _ -> Left $ MkNotImplies impl

verifyUsingContradiction 
  :: StatementsUniverse 
  -> Label 
  -> TacticResult ()
verifyUsingContradiction u l
  = do
      s <- lookUpStatement u l
      case s of
        MkContradiction -> Right ()
        _ -> Left $ MkNotAContradiction s

verifyLawOfExcludedMiddle :: Statement -> TacticResult ()
verifyLawOfExcludedMiddle (MkOr lhs (MkNot rhs))
  | lhs == rhs = Right ()
verifyLawOfExcludedMiddle (MkOr (MkNot lhs) rhs)
  | lhs == rhs = Right ()
verifyLawOfExcludedMiddle stmt
  = Left $ MkNotExcludedMiddle stmt

verifyStep
  :: StatementsUniverse
  -> Statement
  -> Tactic
  -> TacticResult ()
verifyStep u s (MkDirect l)
  = do
      s' <- lookUpStatement u l
      if s' == s then Right () else Left $ MkDirectProofMismatch s s'
verifyStep u s (MkShowingAnd ll lr)
  = verifyShowingAnd u ll lr s
verifyStep u s (MkShowingOr lbase)
  = verifyShowingOr u lbase s
verifyStep u s (MkShowingNot la ctx)
  = verifyShowingNot u la ctx s
verifyStep u s (MkShowingImplies la ctx)
  = verifyShowingImplies u la ctx s
verifyStep u s (MkShowingContradiction ll lr)
  = verifyShowingContradiction u ll lr s
verifyStep u s (MkUsingAnd lbase)
  = verifyUsingAnd u lbase s
verifyStep u s (MkUsingOr lbase ll lr lctx rctx)
  = verifyUsingOr u lbase ll lr lctx rctx s
verifyStep u s (MkUsingImplies lin lim)
  = verifyUsingImplies u lin lim s
verifyStep u s (MkUsingContradiction l)
  = verifyUsingContradiction u l
verifyStep _ s MkExcludedMiddle
  = verifyLawOfExcludedMiddle s
verifyStep u s MkTakeForGranted
  = Right ()

checkLabelAvailability :: StatementsUniverse -> Label -> Statement -> ContextResult ()
checkLabelAvailability u l s
  = case lookUpStatement u l of
      Left _ -> Right ()
      Right olds -> Left $ MkShadowing l olds s

verifyContext
  :: StatementsUniverse
  -> Statement
  -> Context
  -> ContextResult ()
verifyContext u es (MkRet s t)
  | es /= s   = Left $ MkInvalidGoalReached es s
  | otherwise = fromReturnTacticResult $ verifyStep u s t
verifyContext u es (MkLetIn l s t rest)
  = 
    do
      fromLetInTacticResult l $ verifyStep u s t
      checkLabelAvailability u l s
      verifyContext u' es rest
      Right ()
  where
    u' = addStatement u s l

type Proof = Context

verifyProof
  :: StatementsUniverse
  -> Proof
  -> ContextResult Statement
verifyProof u (MkRet s t)
  = fromReturnTacticResult $ verifyStep u s t >> return s
verifyProof u (MkLetIn l s t rest)
  = 
    do
      fromLetInTacticResult l $ verifyStep u s t
      checkLabelAvailability u l s
      verifyProof u' rest
  where
    u' = addStatement u s l

main :: IO ()
main = do
  args <- Env.getArgs
  case args of
    ["check", filename] -> 
      do
        source <- readFile filename
        let body = read source :: Proof
        
        let res = verifyProof [] body
        case res of
          Left e -> 
            print e
          Right stmt -> 
            putStrLn $ "Successfully reached proof goal \"" ++ show stmt ++ "\""
    _ -> putStrLn "usage: runghc ProofAssistant.hs check <input file>"
