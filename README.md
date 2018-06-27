# mwmatching
## Weighted maximum matching in general graphs.

This is a Rust re-implementation of a Python program by Joris van Rantwijk.
Nearly all of the comments are taken directly from that version.
For the original code, go to http://jorisvr.nl/article/maximum-matching.

Compute a maximum-weighted matching in the general undirected
weighted graph given by "edges".  
General usage:
  let mates = matching.new(edges).solve();
or
  let mates = matching.new(edges).max_cardinality().solve();

If "max_cardinality()" is used, then only maximum-cardinality matchings are considered as solutions.

Edges is a sequence of tuples (i, j, wt) describing an undirected
edge between vertex i and vertex j with weight wt.  Currently, wt must be an i32. 
There is at most
one edge between any two vertices; no vertex has an edge to itself.
Vertices are identified by consecutive, non-negative integers (usize).

Returns a list "mates", such that mates[i] == j if vertex i is
matched to vertex j, and mates[i] == SENTINEL if vertex i is not matched,
where SENTINEL is usize::max_value().
