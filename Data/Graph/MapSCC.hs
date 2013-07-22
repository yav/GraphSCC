-- | Implements Tarjan's algorithm for computing the strongly connected
-- components of a graph.  For more details see:
-- <http://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm>.
--
-- This implementation uses 'IntMap' instead of mutable arrays in the algorithm.
-- The benefit is that the implementation conforms to the Haskell 98 standard,
-- however, the algorithm is a bit slower on large graphs.
{-# LANGUAGE Safe #-}
module Data.Graph.MapSCC(scc) where

import Data.Graph(Graph,Vertex)
import qualified Data.IntMap as Map
import Data.Array
import Control.Monad(ap)
import Data.List(foldl')

-- | Computes the strongly connected components (SCCs) in the graph in O(???)
-- time.  The resulting tuple contains:
--   * A (reversed) topologically sorted list of SCCs.
--     Each SCCs is assigned a unique identifier of type 'Int'.
--   * An O(log(V)) mapping from vertices in the original graph to
--     the identifier of their SCC.  This mapping will raise an exception
--     if it is applied to integers that do not correspond to
--     vertices in the input graph.
--
-- This function assumes that the adjacency lists in the original graph
-- mention only nodes that are in the graph. Violating this assumption
-- will result in an exception.
scc :: Graph -> ([(Int,[Vertex])], Vertex -> Int)
scc g =
  let s = roots g (S Map.empty Map.empty [] 1 [] 1) (indices g)
      sccm = ixes s
  in (sccs s, \i -> Map.findWithDefault (err i) i sccm)
  where err i = error $ show i ++ " is not a vertex in the graph"


data S = S { ixes     :: !(Map.IntMap Int)
    -- ^ Index in DFS traversal, or SCC for vertex.
    -- Legend for the index array:
    --    -ve:  Node is on the stack with the given number
    --    +ve:  Node belongs to the SCC with the given number

           , lows     :: !(Map.IntMap Int)  -- ^ Least reachable node
           , stack    :: ![Vertex]          -- ^ Traversal stack
           , num      :: !Int               -- ^ Next node number
           , sccs     :: ![(Int,[Vertex])]  -- ^ Finished SCCs
           , next_scc :: !Int               -- ^ Next SCC number
           }

roots :: Graph -> S -> [Vertex] -> S
roots g st (v:vs) =
  case Map.lookup v (ixes st) of
    Just {} -> roots g st vs
    Nothing -> roots g (from_root g st v) vs
roots _ s [] = s


from_root :: Graph -> S -> Vertex -> S
from_root g s v =
  let me    = num s
      newS  = check_adj g
                    s { ixes = Map.insert v (negate me) (ixes s)
                      , lows = Map.insert v me (lows s)
                      , stack = v : stack s, num = me + 1 } v (g ! v)
  in case Map.lookup v (lows newS) of
       Just x
         | x < me -> newS
         | otherwise ->
            case span (/= v) (stack newS) of
              (as,b:bs) ->
                let this = b : as
                    n = next_scc newS
                    ixes' = foldl' (\m i -> Map.insert i n m) (ixes newS) this
                in   S { ixes = ixes'
                       , lows = lows newS
                       , stack = bs
                       , num = num newS
                       , sccs = (n,this) : sccs newS
                       , next_scc = n + 1
                       }
              _ -> error ("bug in scc---vertex not on the stack: " ++ show v)
       Nothing -> error ("bug in scc--vertex disappeared from lows: " ++ show v)

check_adj :: Graph -> S -> Vertex -> [Vertex] -> S
check_adj g st v (v':vs) =
  case Map.lookup v' (ixes st) of
    Nothing ->
      let newS = from_root g st v'
          Just new_low = min `fmap` Map.lookup v (lows newS)
                               `ap` Map.lookup v' (lows newS)
          lows' = Map.insert v new_low (lows newS)
      in check_adj g newS { lows = lows' } v vs
    Just i
      | i < 0 -> let lows' = Map.adjust (min (negate i)) v (lows st)
                 in check_adj g st { lows = lows' } v vs
      | otherwise -> check_adj g st v vs

check_adj _ st _ [] = st


