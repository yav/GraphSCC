-- | Implements Tarjan's algorithm for computing the strongly connected
-- components of a graph.  For more details see:
-- <http://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm>
{-# LANGUAGE Rank2Types, Trustworthy #-}
module Data.Graph.ArraySCC(scc) where

import Data.Graph(Graph,Vertex)
import Data.Array.ST(STUArray, newArray, readArray, writeArray)
import Data.Array as A
import Data.Array.Unsafe(unsafeFreeze)
import Control.Monad.ST
import Control.Monad(ap)

-- | Computes the strongly connected components (SCCs) of the graph in
-- O(#edges + #vertices) time.  The resulting tuple contains:
--
--   * A (reversed) topologically sorted list of SCCs.
--     Each SCCs is assigned a unique identifier of type 'Int'.
--
--   * An O(1) mapping from vertices in the original graph to the identifier
--     of their SCC.  This mapping will raise an \"out of bounds\"
--     exception if it is applied to integers that do not correspond to
--     vertices in the input graph.
--
-- This function assumes that the adjacency lists in the original graph
-- mention only nodes that are in the graph. Violating this assumption
-- will result in \"out of bounds\" array exception.
scc :: Graph -> ([(Int,[Vertex])], Vertex -> Int)
scc g = runST (
  do ixes <- newArray (bounds g) 0
     lows <- newArray (bounds g) 0
     s <- roots g ixes lows (S [] 1 [] 1) (indices g)
     sccm <- unsafeFreeze ixes
     return (sccs s, \i -> sccm ! i)
  )

type Func s a =
     Graph                    -- The original graph
  -> STUArray s Vertex Int    -- Index in DFS traversal, or SCC for vertex.
    -- Legend for the index array:
    --    0:    Node not visited
    --    -ve:  Node is on the stack with the given number
    --    +ve:  Node belongs to the SCC with the given number
  -> STUArray s Vertex Int    -- Least reachable node
  -> S                        -- State
  -> a

data S = S { stack    :: ![Vertex]          -- ^ Traversal stack
           , num      :: !Int               -- ^ Next node number
           , sccs     :: ![(Int,[Vertex])]  -- ^ Finished SCCs
           , next_scc :: !Int               -- ^ Next SCC number
           }


roots :: Func s ([Vertex] -> ST s S)
roots g ixes lows st (v:vs) =
  do i <- readArray ixes v
     if i == 0 then do s1 <- from_root g ixes lows st v
                       roots g ixes lows s1 vs
               else roots g ixes lows st vs
roots _ _ _ s [] = return s


from_root :: Func s (Vertex -> ST s S)
from_root g ixes lows s v =
  do let me = num s
     writeArray ixes v (negate me)
     writeArray lows v me
     newS <- check_adj g ixes lows
                        s { stack = v : stack s, num = me + 1 } v (g ! v)

     x <- readArray lows v
     if x < me then return newS else
       case span (/= v) (stack newS) of
         (as,b:bs) ->
           do let this = b : as
                  n = next_scc newS
              mapM_ (\i -> writeArray ixes i n) this
              return S { stack = bs
                       , num = num newS
                       , sccs = (n,this) : sccs newS
                       , next_scc = n + 1
                       }
         _ -> error ("bug in scc---vertex not on the stack: " ++ show v)

check_adj :: Func s (Vertex -> [Vertex] -> ST s S)
check_adj g ixes lows st v (v':vs) =
  do i <- readArray ixes v'
     case () of
       _ | i == 0 ->
             do newS <- from_root g ixes lows st v'
                new_low <- min `fmap` readArray lows v `ap` readArray lows v'
                writeArray lows v new_low
                check_adj g ixes lows newS v vs
         | i < 0 ->
             do j <- readArray lows v
                writeArray lows v (min j (negate i))
                check_adj g ixes lows st v vs
         | otherwise -> check_adj g ixes lows st v vs
check_adj _ _ _ st _ [] = return st


