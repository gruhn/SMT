module CLI where

import qualified Algorithm.CDCL2 as CDCL
import CNF
import Assignment
import Expression


satWith :: (CNF (WithAux String) -> Maybe (Assignment (WithAux String)))
        -> Expr String
        -> Maybe (Assignment String)
satWith sat = 
    fmap ignoreAuxVars
  . sat 
  . conjunctiveNormalForm 
  . tseytin 

data Theory = PROP | UF | LIA | LRA | NRA

x = Atom "x"
y = Atom "y"
z = Atom "z"

-- | Enter and check formula for satisfiability.
check :: Theory -> Expr String -> IO ()
check PROP input = 
  print $ satWith CDCL.sat input
check _ _ = error "TODO: theory not supported yet"
