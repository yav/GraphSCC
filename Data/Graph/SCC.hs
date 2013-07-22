{-# LANGUAGE CPP, Safe #-}
module Data.Graph.SCC
  ( scc
  , sccList
  , sccListR
  , sccGraph
  , stronglyConnComp
  , stronglyConnCompR
  ) where

#ifdef USE_MAPS
import Data.Graph.MapSCC
#else
import Data.Graph.ArraySCC
#endif
import Data.Graph(SCC(..),Graph,Vertex,graphFromEdges')

import Data.Array as A
import Data.List(nub)

-- | Compute the list of strongly connected components of a graph.
-- The components are topologically sorted:
-- if v1 in C1 points to v2 in C2, then C2 will come before C1 in the list.
sccList :: Graph -> [SCC Vertex]
sccList g = reverse $ map (to_scc g lkp) cs
  where (cs,lkp) = scc g

-- | Compute the list of strongly connected components of a graph.
-- Each component contains the adjecency information from the original graph.
-- The components are topologically sorted:
-- if v1 in C1 points to v2 in C2, then C2 will come before C1 in the list.
sccListR :: Graph -> [SCC (Vertex,[Vertex])]
sccListR g = reverse $ map cvt cs
  where (cs,lkp) = scc g
        cvt (n,[v]) = let adj = g ! v
                      in if  n `elem` map lkp adj
                           then CyclicSCC [(v,adj)]
                           else AcyclicSCC (v,adj)
        cvt (_,vs)  = CyclicSCC [ (v, g ! v) | v <- vs ]

-- | Quotient a graph with the relation that relates vertices that
-- belong to the same SCC.  The vertices in the new graph are the
-- SCCs of the old graph, and there is an edge between two components,
-- if there is an edge between any of their vertices.
-- The entries in the resulting list are in reversed-topologically sorted:
-- if v1 in C1 points to v2 in C2, then C1 will come before C2 in the list.
sccGraph :: Graph -> [(SCC Int, Int, [Int])]
sccGraph g = map to_node cs
  where (cs,lkp) = scc g
        to_node x@(n,this) = ( to_scc g lkp x
                             , n
                             , nub $ concatMap (map lkp . (g !)) this
                             )


stronglyConnComp :: Ord key => [(node, key, [key])] -> [SCC node]
stronglyConnComp es = reverse $ map cvt cs
  where (g,back)    = graphFromEdges' es
        (cs,lkp)    = scc g
        cvt (n,[v]) = let (node,_,_) = back v
                      in if n `elem` map lkp (g ! v)
                            then CyclicSCC [node]
                            else AcyclicSCC node
        cvt (_,vs)  = CyclicSCC [ node | (node,_,_) <- map back vs ]


stronglyConnCompR :: Ord key => [(node, key, [key])] -> [SCC (node, key, [key])]
stronglyConnCompR es = reverse $ map cvt cs
  where (g,back)    = graphFromEdges' es
        (cs,lkp)    = scc g
        cvt (n,[v]) = if n `elem` map lkp (g ! v)
                         then CyclicSCC [back v]
                         else AcyclicSCC (back v)
        cvt (_,vs)  = CyclicSCC (map back vs)



--------------------------------------------------------------------------------
to_scc :: Graph -> (Vertex -> Int) -> (Int,[Vertex]) -> SCC Vertex
to_scc g lkp (n,[v]) = if n `elem` map lkp (g ! v) then CyclicSCC [v]
                                                   else AcyclicSCC v
to_scc _ _ (_,vs)    = CyclicSCC vs


