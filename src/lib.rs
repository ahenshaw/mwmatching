// Weighted maximum matching in general graphs.

// This is a Rust re-implementation of a Python program by Joris van Rantwijk.
// Nearly all of the comments are taken directly from that version.
// For his original code, go to http://jorisvr.nl/article/maximum-matching.

// The algorithm is taken from "Efficient Algorithms for Finding Maximum
// Matching in Graphs" by Zvi Galil, ACM Computing Surveys, 1986.
// It is based on the "blossom" method for finding augmenting paths and
// the "primal-dual" method for finding a matching of maximum weight, both
// due to Jack Edmonds.
// Some ideas came from "Implementation of algorithms for maximum matching
// on non-bipartite graphs" by H.J. Gabow, Standford Ph.D. thesis, 1973.

/// Compute a maximum-weighted matching in the general undirected
/// weighted graph given by "edges".  If "maxcardinality" is true,
/// only maximum-cardinality matchings are considered as solutions.

/// Edges is a sequence of tuples (i, j, wt) describing an undirected
/// edge between vertex i and vertex j with weight wt.  There is at most
/// one edge between any two vertices; no vertex has an edge to itself.
/// Vertices are identified by consecutive, non-negative integers.

/// Return a list "mate", such that mate[i] == j if vertex i is
/// matched to vertex j, and mate[i] == SENTINEL if vertex i is not matched.

/// This function takes time O(n ** 3)."""

use std::cmp::max;

pub type Vertex   = usize;
pub type Vertices = Vec<Vertex>;
pub type Weight   = i32;
pub type Weights  = Vec<Weight>;
pub type Edge     = (Vertex, Vertex, Weight); // i, j, wt
pub type Edges    = Vec<Edge>;

pub const SENTINEL:Vertex    = <Vertex>::max_value();

const CHECK_DELTA:bool   = false;
const CHECK_OPTIMUM:bool = true;

#[derive(Debug, Default)]
pub struct Matching {
    nvertex:   usize,
    nedge:     usize,
    maxweight: Weight,  
    edges:     Edges,
    dualvar:          Weights,
    endpoint:         Vertices,
    label:            Vertices,
    labelend:         Vertices,
    inblossom:        Vertices,
    blossombase:      Vertices,
    blossomparent:    Vertices,
    bestedge:         Vertices,
    unusedblossoms:   Vertices,
    mate:             Vertices,
    queue:            Vertices,
    blossombestedges: Vec<Vertices>,
    blossomchilds:    Vec<Vertices>, 
    blossomendps:     Vec<Vertices>,
    neighbend:        Vec<Vertices>,
    allowedge:        Vec<bool>,
    maxcardinality:   bool,
}

impl Matching {
    pub fn new(edges: Edges) -> Matching {
        let mut matching = Matching::default();
        matching.edges = edges;
        if matching.edges.len() > 0 {
            matching.initialize();
        }
        matching
    }

    fn initialize(&mut self){

        // 
        // Vertices are numbered 0 .. (nvertex-1).
        // Non-trivial blossoms are numbered nvertex .. (2*nvertex-1)
        //
        // Edges are numbered 0 .. (nedge-1).
        // Edge endpoints are numbered 0 .. (2*nedge-1), such that endpoints
        // (2*k) and (2*k+1) both belong to edge k.
        //
        // Many terms used in the comments (sub-blossom, T-vertex) come from
        // the paper by Galil; read the paper before reading this code.
        //

        self.nedge = self.edges.len();

        // Count vertices.
        self.nvertex = 0;

        // override with max_cardinality function call
        self.maxcardinality = false;


        for &(i, j, _wt) in &self.edges {
            assert!(i != j);
            if i >= self.nvertex {
                self.nvertex = i + 1;
            }
            if j >= self.nvertex{
                self.nvertex = j + 1;
            }
        }

        //// Find the maximum edge weight.
        self.maxweight = self.edges.iter().max_by_key(|x| x.2).unwrap().2;

        // If p is an edge endpoint,
        // endpoint[p] is the vertex to which endpoint p is attached.
        // Not modified by the algorithm.
        self.endpoint = (0..2*self.nedge).map(|x| 
                                        if x%2==0 {self.edges[x/2].0} 
                                        else {self.edges[x/2].1})
                                    .collect();

        self.neighbend = vec![vec![]; self.nvertex];
        for (k, &(i, j, _wt)) in self.edges.iter().enumerate() {
            self.neighbend[i].push(2*k+1);
            self.neighbend[j].push(2*k);
        }

        // If v is a vertex,
        // mate[v] is the remote endpoint of its matched edge, or SENTINEL if it is single
        // (i.e. endpoint[mate[v]] is v's partner vertex).
        // Initially all vertices are single; updated during augmentation.
        self.mate = vec![SENTINEL; self.nvertex];

        // If b is a top-level blossom,
        // label[b] is 0 if b is unlabeled (free);
        //             1 if b is an S-vertex/blossom;
        //             2 if b is a T-vertex/blossom.
        // The label of a vertex is found by looking at the label of its
        // top-level containing blossom.
        // If v is a vertex inside a T-blossom,
        // label[v] is 2 iff v is reachable from an S-vertex outside the blossom.
        // Labels are assigned during a stage and reset after each augmentation.
        self.label = vec![0; 2*self.nvertex];

        // If b is a labeled top-level blossom,
        // labelend[b] is the remote endpoint of the edge through which b obtained
        // its label, or SENTINEL if b's base vertex is single.
        // If v is a vertex inside a T-blossom and label[v] == 2,
        // labelend[v] is the remote endpoint of the edge through which v is
        // reachable from outside the blossom.
        self.labelend = vec![SENTINEL; 2 * self.nvertex];

        // If v is a vertex,
        // inblossom[v] is the top-level blossom to which v belongs.
        // If v is a top-level vertex, v is itself a blossom (a trivial blossom)
        // and inblossom[v] == v.
        // Initially all vertices are top-level trivial blossoms.
        self.inblossom = (0..self.nvertex).collect();

        // If b is a sub-blossom,
        // blossomparent[b] is its immediate parent (sub-)blossom.
        // If b is a top-level blossom, blossomparent[b] is SENTINEL.
        self.blossomparent = vec![SENTINEL; 2*self.nvertex];

        // If b is a non-trivial (sub-)blossom,
        // blossomchilds[b] is an ordered list of its sub-blossoms, starting with
        // the base and going round the blossom.
        self.blossomchilds = vec![vec![]; 2*self.nvertex];

        // If b is a (sub-)blossom,
        // blossombase[b] is its base VERTEX (i.e. recursive sub-blossom).
        self.blossombase = (0..(self.nvertex)).collect(); 
        self.blossombase.extend(vec![SENTINEL; self.nvertex]);

        // If b is a non-trivial (sub-)blossom,
        // blossomendps[b] is a list of endpoints on its connecting edges,
        // such that blossomendps[b][i] is the local endpoint of blossomchilds[b][i]
        // on the edge that connects it to blossomchilds[b][wrap(i+1)].
        self.blossomendps = vec![vec![]; 2*self.nvertex];

        // If v is a free vertex (or an unreached vertex inside a T-blossom),
        // bestedge[v] is the edge to an S-vertex with least slack,
        // or SENTINEL if there is no such edge.
        // If b is a (possibly trivial) top-level S-blossom,
        // bestedge[b] is the least-slack edge to a different S-blossom,
        // or SENTINEL if there is no such edge.
        // This is used for efficient computation of delta2 and delta3.
        self.bestedge = vec![SENTINEL; 2*self.nvertex];

        // If b is a non-trivial top-level S-blossom,
        // blossombestedges[b] is a list of least-slack edges to neighbouring
        // S-blossoms, or None if no such list has been computed yet.
        // This is used for efficient computation of delta3.
        self.blossombestedges = vec![vec![]; 2*self.nvertex];

        // List of currently unused blossom numbers.
        self.unusedblossoms = (self.nvertex..2*self.nvertex).collect();

        // If v is a vertex,
        // dualvar[v] = 2 * u(v) where u(v) is the v's variable in the dual
        // optimization problem (multiplication by two ensures integer values
        // throughout the algorithm if all edge weights are integers).
        // If b is a non-trivial blossom,
        // dualvar[b] = z(b) where z(b) is b's variable in the dual optimization
        // problem.
        self.dualvar = vec![self.maxweight;self.nvertex];
        self.dualvar.extend(vec![0; self.nvertex]);

        // If allowedge[k] is true, edge k has zero slack in the optimization
        // problem; if allowedge[k] is false, the edge's slack may or may not
        // be zero.
        self.allowedge = vec![false; self.nedge];

        // Queue of newly discovered S-vertices.
        self.queue = vec![];
    }

    // Return 2 * slack of edge k (does not work inside blossoms).
    #[inline]
    fn slack(&self, k:Vertex) -> Weight {
        let (i, j, wt) = self.edges[k];
        self.dualvar[i] + self.dualvar[j] - 2 * wt
    }

    /// Generate the leaf vertices of a blossom.
    fn blossom_leaves(&self, b: Vertex) -> Vertices {
        let mut leaves: Vertices = vec![];
        if b < self.nvertex {
            leaves.push(b);
        } else {
            for &t in &self.blossomchilds[b] {
                if t < self.nvertex {
                    leaves.push(t);
                } else {
                    leaves.extend(self.blossom_leaves(t));
                }
            }
        }
        leaves
    }

    /// Assign label t to the top-level blossom containing vertex w
    /// and record the fact that w was reached through the edge with
    /// remote endpoint p.
    fn assign_label(&mut self, w: Vertex, t: Vertex, p: Vertex) {
        let b = self.inblossom[w];
        assert!(self.label[w] == 0 && self.label[b] == 0);

        self.label[w]    = t; 
        self.label[b]    = t;
        self.labelend[w] = p;
        self.labelend[b] = p;
        self.bestedge[w] = SENTINEL;
        self.bestedge[b] = SENTINEL;

        if t == 1 {
            // b became an S-vertex/blossom; add it(s vertices) to the queue.
            let leaves = self.blossom_leaves(b);
            self.queue.extend(leaves);
        } else if t == 2 {
            // b became a T-vertex/blossom; assign label S to its mate.
            // (If b is a non-trivial blossom, its base is the only vertex
            // with an external mate.)
            let base = self.blossombase[b];
            assert!(self.mate[base] != SENTINEL);
            let mbase    = self.mate[base];
            let endpoint = self.endpoint[mbase];
            self.assign_label(endpoint, 1, mbase ^ 1);
        }
    }

    // Trace back from vertices v and w to discover either a new blossom
    // or an augmenting path. Return the base vertex of the new blossom or -1.
    fn scan_blossom(&mut self, v:Vertex, w:Vertex) -> Vertex {
        // Trace back from v and w, placing breadcrumbs as we go.
        let mut path = vec![];
        let mut base = SENTINEL;
        let mut v    = v;
        let mut w    = w;
        while v != SENTINEL || w != SENTINEL{
            // Look for a breadcrumb in v's blossom or put a new breadcrumb.
            let mut b = self.inblossom[v];
            if (self.label[b] & 4) != 0 {
                base = self.blossombase[b];
                break
            }
            assert!(self.label[b] == 1);
            path.push(b);
            self.label[b] = 5;
            // Trace one step back.
            assert!(self.labelend[b] == self.mate[self.blossombase[b]]);
            if self.labelend[b] == SENTINEL {
                // The base of blossom b is single; stop tracing this path.
                v = SENTINEL;
            } else {
                v = self.endpoint[self.labelend[b]];
                b = self.inblossom[v];
                assert!(self.label[b] == 2);
                // b is a T-blossom; trace one more step back.
                assert!(self.labelend[b] != SENTINEL);
                v = self.endpoint[self.labelend[b]];
            }
            // Swap v and w so that we alternate between both paths.
            if w != SENTINEL {
                std::mem::swap(&mut v, &mut w);
            }
        }
        // Remove breadcrumbs.
        for b in path {
            self.label[b] = 1;
        }
        // Return base vertex, if we found one.
        base
    }
    /// Construct a new blossom with given base, containing edge k which
    /// connects a pair of S vertices. Label the new blossom as S; set its dual
    /// variable to zero; relabel its T-vertices to S and add them to the queue.
    fn add_blossom(&mut self, base: Vertex, k: usize) {
        let (mut v, mut w, _wt) = self.edges[k];
        let bb = self.inblossom[base];
        let mut bv = self.inblossom[v];
        let mut bw = self.inblossom[w];

        // Create blossom.
        let b = self.unusedblossoms.pop().unwrap();
        self.blossombase[b]    = base;
        self.blossomparent[b]  = SENTINEL;
        self.blossomparent[bb] = b;

        // Make list of sub-blossoms and their interconnecting edge endpoints.
        self.blossomchilds[b] = vec![];
        self.blossomendps[b]  = vec![];

        // Trace back from v to base.
        while bv != bb {
            // Add bv to the new blossom.
            self.blossomparent[bv] = b;
            self.blossomchilds[b].push(bv);

            self.blossomendps[b].push(self.labelend[bv]);

            assert!(self.label[bv] == 2 
                   || (self.label[bv] == 1 
                       && (self.labelend[bv] == self.mate[self.blossombase[bv]])));
            // Trace one step back.
            assert!(self.labelend[bv] != SENTINEL);
            v = self.endpoint[self.labelend[bv]];
            bv = self.inblossom[v];
        }

        // Reverse lists, add endpoint that connects the pair of S vertices.
        self.blossomchilds[b].push(bb);
        self.blossomchilds[b].reverse();
        self.blossomendps[b].reverse();
        self.blossomendps[b].push(2*k);

        // Trace back from w to base.
        while bw != bb {
            // Add bw to the new blossom.
            self.blossomparent[bw] = b;
            self.blossomchilds[b].push(bw);
            self.blossomendps[b].push(self.labelend[bw] ^ 1);
            assert!(self.label[bw] == 2 ||
                    (self.label[bw] == 1 
                    && (self.labelend[bw] == self.mate[self.blossombase[bw]])));

            // Trace one step back.
            assert!(self.labelend[bw] != SENTINEL);
            w  = self.endpoint[self.labelend[bw]];
            bw = self.inblossom[w];
        }

        // Set label to S.
        assert!(self.label[bb] == 1);
        self.label[b] = 1;
        self.labelend[b] = self.labelend[bb];
        
        // Set dual variable to zero.
        self.dualvar[b] = 0;
        
        // Relabel vertices.
        for v in self.blossom_leaves(b) {
            if self.label[self.inblossom[v]] == 2 {
                // This T-vertex now turns into an S-vertex because it becomes
                // part of an S-blossom; add it to the queue.
                self.queue.push(v);
            }
            self.inblossom[v] = b;
        }
        // Compute blossombestedges[b].
        let mut bestedgeto = vec![SENTINEL; 2*self.nvertex];
        for &bv in &self.blossomchilds[b] {
            let mut nblists = vec![];

            if self.blossombestedges[bv].len() == 0 {
                // This subblossom does not have a list of least-slack edges;
                // get the information from the vertices.
                for v in self.blossom_leaves(bv) {
                    nblists.push(self.neighbend[v].iter().map(|p| p/2).collect());
                }
            } else {
                // Walk this subblossom's least-slack edges.
                let bbe = self.blossombestedges[bv].clone();
                nblists.push(bbe);
            }
            for nblist in nblists {
                for k in nblist {
                    let (mut i, mut j, _wt) = self.edges[k];
                    if self.inblossom[j] == b {
                        std::mem::swap(&mut i, &mut j);
                    }
                    let bj = self.inblossom[j];
                    let bestto = bestedgeto[bj];
                    if (bj != b) 
                        && (self.label[bj] == 1)
                        && (bestto == SENTINEL || (self.slack(k) < self.slack(bestto))) {
                        bestedgeto[bj] = k;
                    }
                }
            }
            // Forget about least-slack edges of the subblossom.
            self.blossombestedges[bv] = vec![];
            self.bestedge[bv] = SENTINEL;
        }
        self.blossombestedges[b] = bestedgeto.iter().filter(|k| **k != SENTINEL).map(|k| *k).collect();

        // Select bestedge[b]
        self.bestedge[b] = SENTINEL;
        for &k in &self.blossombestedges[b] {
            let be = self.bestedge[b];
            if (be == SENTINEL) || (self.slack(k) < self.slack(be)) {
                self.bestedge[b] = k;
            }
        }
    }

    /// Expand the given top-level blossom.
    fn expand_blossom(&mut self, b: Vertex, endstage: bool) {
        // Convert sub-blossoms into top-level blossoms.
        for s in self.blossomchilds[b].clone() {
            self.blossomparent[s] = SENTINEL;
            if s < self.nvertex {
                self.inblossom[s] = s;
            } else if endstage && (self.dualvar[s] == 0) {
                // Recursively expand this sub-blossom.
                self.expand_blossom(s, endstage);
            } else {
                for &v in &self.blossom_leaves(s) {
                    self.inblossom[v] = s;
                }
            }
        }

        // If we expand a T-blossom during a stage, its sub-blossoms must be
        // relabeled.
        if !endstage && (self.label[b] == 2) {
            // Start at the sub-blossom through which the expanding
            // blossom obtained its label, and relabel sub-blossoms until
            // we reach the base.
            // Figure out through which sub-blossom the expanding blossom
            // obtained its label initially.
            assert!(self.labelend[b] != SENTINEL);
            let entrychild = self.inblossom[self.endpoint[self.labelend[b] ^ 1]];

            // Decide in which direction we will go round the blossom.
            let mut j:i32 = self.blossomchilds[b].iter().position(|r| *r==entrychild).unwrap() as i32;
            let jstep: i32;
            let endptrick: usize;
            if (j & 1) != 0 {
                // Start index is odd; go forward and wrap.
                j -= self.blossomchilds[b].len() as i32;
                jstep = 1;
                endptrick = 0;
            } else {
                // Start index is even; go backward.
                jstep = -1;
                endptrick = 1;
            }

            // Move along the blossom until we get to the base.
            let mut p = self.labelend[b];
            while j != 0 {
                // Relabel the T-sub-blossom.
                self.label[self.endpoint[p ^ 1]] = 0;
                self.label[self.endpoint[pos_neg_index(&self.blossomendps[b], j-endptrick as i32)^endptrick^1]] = 0;
                let ep = self.endpoint[p ^ 1];
                self.assign_label(ep, 2, p);

                // Step to the next S-sub-blossom and note its forward endpoint.
                self.allowedge[pos_neg_index(&self.blossomendps[b], j-endptrick as i32)/2] = true;
                j += jstep;
                p = pos_neg_index(&self.blossomendps[b], j-endptrick as i32) ^ endptrick;

                // Step to the next T-sub-blossom.
                self.allowedge[p/2] = true;
                j += jstep;
            }

            // Relabel the base T-sub-blossom WITHOUT stepping through to
            // its mate (so don't call assignLabel).
            let bv = pos_neg_index(&self.blossomchilds[b], j);
            self.label[self.endpoint[p ^ 1]] = 2;
            self.label[bv] = 2;

            self.labelend[self.endpoint[p ^ 1]] = p;
            self.labelend[bv] = p;

            self.bestedge[bv] = SENTINEL;

            // Continue along the blossom until we get back to entrychild.
            j += jstep;

            while pos_neg_index(&self.blossomchilds[b], j) != entrychild {
                // Examine the vertices of the sub-blossom to see whether
                // it is reachable from a neighbouring S-vertex outside the
                // expanding blossom.
                let bv = pos_neg_index(&self.blossomchilds[b], j);
                if self.label[bv] == 1 {
                    // This sub-blossom just got label S through one of its
                    // neighbours; leave it.
                    j += jstep;
                    continue;
                }
                let mut v: Vertex = SENTINEL;
                for &temp in &self.blossom_leaves(bv) {
                    v = temp;
                    if self.label[v] != 0 {
                        break;
                    }
                }
                // If the sub-blossom contains a reachable vertex, assign
                // label T to the sub-blossom.
                if self.label[v] != 0 {
                    assert!(self.label[v] == 2);
                    assert!(self.inblossom[v] == bv);
                    self.label[v] = 0;
                    self.label[self.endpoint[self.mate[self.blossombase[bv]]]] = 0;
                    let lblend = self.labelend[v];
                    self.assign_label(v, 2, lblend);
                }
                j += jstep;
            }
        }
        // Recycle the blossom number.
        self.label[b]       = SENTINEL;
        self.labelend[b]    = SENTINEL;
        self.blossombase[b] = SENTINEL;
        self.bestedge[b]    = SENTINEL;

        self.blossomchilds[b]    = vec![];
        self.blossomendps[b]     = vec![];
        self.blossombestedges[b] = vec![];

        self.unusedblossoms.push(b);
    }

    /// Swap matched/unmatched edges over an alternating path through blossom b
    /// between vertex v and the base vertex. Keep blossom bookkeeping consistent.
    fn augment_blossom(&mut self, b: Vertex, v: Vertex) {
        // Bubble up through the blossom tree from vertex v to an immediate
        // sub-blossom of b.
        let mut t = v;
        while self.blossomparent[t] != b {
            t = self.blossomparent[t];
        }

        // Recursively deal with the first sub-blossom.
        if (t != SENTINEL) && (t >= self.nvertex) {
            self.augment_blossom(t, v);
        }

        // Decide in which direction we will go round the blossom.
        let i = self.blossomchilds[b].iter().position(|r| *r==t).unwrap();
        let mut j:i32 = i as i32;
        let jstep:i32;
        let endptrick;
        if (i & 1) != 0 {
            // Start index is odd; go forward and wrap.
            j -= self.blossomchilds[b].len() as i32;
            jstep = 1;
            endptrick = 0;
        } else {
            // Start index is even; go backward.
            jstep = -1;
            endptrick = 1;
        }

        // Move along the blossom until we get to the base.
        while j != 0 {
            // Step to the next sub-blossom and augment it recursively.
            j += jstep;
            let mut t = pos_neg_index(&self.blossomchilds[b], j);
            let p = pos_neg_index(&self.blossomendps[b], j-endptrick as i32) ^ endptrick;
            if (t !=SENTINEL) && (t >= self.nvertex) {
                let endp = self.endpoint[p];
                self.augment_blossom(t, endp);
            }

            // Step to the next sub-blossom and augment it recursively.
            if jstep == 1 {
                j += 1;
            } else {
                j -= 1;
            }
            t = pos_neg_index(&self.blossomchilds[b], j);
            if (t !=SENTINEL) && (t >= self.nvertex) {
                let endp = self.endpoint[p ^ 1];
                self.augment_blossom(t, endp);
            }
            // Match the edge connecting those sub-blossoms.
            self.mate[self.endpoint[p]] = p ^ 1;
            self.mate[self.endpoint[p ^ 1]] = p;
        }
        // Rotate the list of sub-blossoms to put the new base at the front.
        rotate(&mut self.blossomchilds[b], i);
        rotate(&mut self.blossomendps[b], i);

        self.blossombase[b] = self.blossombase[self.blossomchilds[b][0]];
        assert!(self.blossombase[b] == v);
    }

    /// Swap matched/unmatched edges over an alternating path between two
    /// single vertices. The augmenting path runs through edge k, which
    /// connects a pair of S vertices.
    fn augment_matching(&mut self, k: Vertex) {
        let (v, w, _wt) = self.edges[k];
        for (mut s, mut p) in vec![(v, 2*k+1), (w, 2*k)].iter() {
            // Match vertex s to remote endpoint p. Then trace back from s
            // until we find a single vertex, swapping matched and unmatched
            // edges as we go.
            loop {
                let bs = self.inblossom[s];
                assert!(self.label[bs] == 1);
                assert!(self.labelend[bs] == self.mate[self.blossombase[bs]]);

                // Augment through the S-blossom from s to base.
                if (bs != SENTINEL) && (bs >= self.nvertex) {
                    self.augment_blossom(bs, s);
                }

                // Update mate[s]
                self.mate[s] = p;

                // Trace one step back.
                if self.labelend[bs] == SENTINEL {
                    // Reached single vertex; stop.
                    break
                }
                let t = self.endpoint[self.labelend[bs]];
                let bt = self.inblossom[t];
                assert!(self.label[bt] == 2);

                // Trace one step back.
                assert!(self.labelend[bt] != SENTINEL);
                s = self.endpoint[self.labelend[bt]];
                let j = self.endpoint[self.labelend[bt] ^ 1];

                // Augment through the T-blossom from j to base.
                assert!(self.blossombase[bt] == t);
                if (bt != SENTINEL) && (bt >= self.nvertex) {
                    self.augment_blossom(bt, j);
                }

                // Update mate[j]
                self.mate[j] = self.labelend[bt];

                // Keep the opposite endpoint;
                // it will be assigned to mate[s] in the next step.
                p = self.labelend[bt] ^ 1;
            }
        }
    }

    /// Verify that the optimum solution has been reached.
    fn verify_optimum(&self) {
        let vdualoffset:Weight;
        if self.maxcardinality {
            // Vertices may have negative dual;
            // find a constant non-negative number to add to all vertex duals.
            vdualoffset = max(0, -(self.dualvar[0..self.nvertex].iter().min().unwrap()));
        } else {
            vdualoffset = 0;
        }
        // 0. all dual variables are non-negative
        //assert min(dualvar[:nvertex]) + vdualoffset >= 0
        //assert min(dualvar[nvertex:]) >= 0
        // 0. all edges have non-negative slack and
        // 1. all matched edges have zero slack;
        for k in 0..self.nedge {
            let (i, j, wt) = self.edges[k];
            let mut s:i32  = self.dualvar[i] + self.dualvar[j] - 2*wt;
            let mut iblossoms = vec![i];
            let mut jblossoms = vec![j];

            while self.blossomparent[*(iblossoms.last().unwrap())] != SENTINEL {
                let &ix = iblossoms.last().unwrap();
                iblossoms.push(self.blossomparent[ix]);
            }
            while self.blossomparent[*(jblossoms.last().unwrap())] != SENTINEL {
                let &jx = jblossoms.last().unwrap();
                jblossoms.push(self.blossomparent[jx]);
            }
            iblossoms.reverse();
            jblossoms.reverse();
            for (&bi, bj) in iblossoms.iter().zip(jblossoms) {
                if bi != bj {
                    break;
                }
                s += 2 * self.dualvar[bi];
            }
            assert!(s >= 0);
            if (self.mate[i] / 2 == k) || (self.mate[j] / 2 == k) {
                assert!(self.mate[i] / 2 == k);
                assert!(self.mate[j] / 2 == k);
                assert!(s == 0);
            }
        }
        // 2. all single vertices have zero dual value;
        for v in 0..self.nvertex {
            assert!((self.mate[v] != SENTINEL) || (self.dualvar[v] + vdualoffset == 0));
        }
        // 3. all blossoms with positive dual value are full.
        for b in self.nvertex..2*self.nvertex {
            if (self.blossombase[b] != SENTINEL) || (self.dualvar[b] > 0) {
                assert!(self.blossomendps[b].len() % 2 == 1);
                for (ix, &p) in self.blossomendps[b].iter().enumerate() {
                    if (ix % 2) == 1 {
                        assert!(self.mate[self.endpoint[p]] == p ^ 1);
                        assert!(self.mate[self.endpoint[p ^ 1]] == p);
                    }
                }
            }
        }
        // Optimum verified
    }
    
    /// Check optimized delta2 against a trivial computation.
    fn check_delta2(&self) {
        for v in 0..self.nvertex {
            if self.label[self.inblossom[v]] == 0 {
                let mut bd = 0;
                let mut bk = SENTINEL;
                for &p in &self.neighbend[v] {
                    let mut k = p / 2;
                    let w = self.endpoint[p];
                    if self.label[self.inblossom[w]] == 1 {
                        let d = self.slack(k);
                        if (bk == SENTINEL) || d < bd {
                            bk = k;
                            bd = d;
                        }
                    }
                }
                assert!(((bk == SENTINEL) 
                    &&   (self.bestedge[v] == SENTINEL)) 
                    ||  ((self.bestedge[v] != SENTINEL) 
                    &&   (bd == self.slack(self.bestedge[v]))));
            }
        }
    }

    /// Check optimized delta3 against a trivial computation.
    fn check_delta3(&self) {
        let mut bk = SENTINEL;
        let mut bd = 0;
        let mut tbk = SENTINEL;
        let mut tbd = 0;

        for b in 0..2*self.nvertex {
            if (self.blossomparent[b] == SENTINEL) && (self.label[b] == 1) {
                for v in self.blossom_leaves(b) {
                    for &p in &self.neighbend[v] {
                        let k = p / 2;
                        let w = self.endpoint[p];
                        if (self.inblossom[w] != b) && (self.label[self.inblossom[w]] == 1) {
                            let d = self.slack(k);
                            if (bk == SENTINEL) || (d < bd) {
                                bk = k;
                                bd = d;
                            }
                        }
                    }
                }
                if self.bestedge[b] != SENTINEL {
                    let (i, j, _wt) = self.edges[self.bestedge[b]];
                    assert!(self.inblossom[i] == b || self.inblossom[j] == b);
                    assert!(self.inblossom[i] != b || self.inblossom[j] != b);
                    assert!(self.label[self.inblossom[i]] == 1 && self.label[self.inblossom[j]] == 1);
                    if (tbk == SENTINEL) || (self.slack(self.bestedge[b]) < tbd) {
                        tbk = self.bestedge[b];
                        tbd = self.slack(self.bestedge[b]);
                    }
                }
            }
        }
        assert!(bd == tbd);
    }

    pub fn solve(&mut self) -> Vertices {
        if self.edges.len() == 0 {
            return vec![];
        }

        // Main loop: continue until no further improvement is possible.
        let mut kslack = 0i32;
        for _t in 0..self.nvertex {

            // Each iteration of this loop is a "stage".
            // A stage finds an augmenting path and uses that to improve
            // the matching.

            // Remove labels from top-level blossoms/vertices.
            self.label = vec![0; 2*self.nvertex];

            // Forget all about least-slack edges.
            self.bestedge = vec![SENTINEL; 2*self.nvertex];
            for ll in self.nvertex..2*self.nvertex {
                self.blossombestedges[ll] = vec![];
            }

            // Loss of labeling means that we can not be sure that currently
            // allowable edges remain allowable througout this stage.
            self.allowedge = vec![false;self.nedge];

            // Make queue empty.
            self.queue = vec![];
    
            // Label single blossoms/vertices with S and put them in the queue.
            for v in 0..self.nvertex {
                if self.mate[v] == SENTINEL && self.label[self.inblossom[v]] == 0 {
                    self.assign_label(v, 1, SENTINEL);
                }
            }
            // Loop until we succeed in augmenting the matching.
            let mut augmented = false;
            loop {
                // Each iteration of this loop is a "substage".
                // A substage tries to find an augmenting path;
                // if found, the path is used to improve the matching and
                // the stage ends. If there is no augmenting path, the
                // primal-dual method is used to pump some slack out of
                // the dual variables.

                // Continue labeling until all vertices which are reachable
                // through an alternating path have got a label.
                while (self.queue.len() != 0) && (!augmented) {
                    // Take an S vertex from the queue.
                    let v = self.queue.pop().unwrap();
                    assert!(self.label[self.inblossom[v]] == 1);
                    // Scan its neighbours:
                    for p in self.neighbend[v].clone() {
                        let mut k = p / 2;
                        let w = self.endpoint[p];
                        // w is a neighbour to v
                        if self.inblossom[v] == self.inblossom[w] {
                            // this edge is internal to a blossom; ignore it
                            continue
                        }
                        if !self.allowedge[k] {
                            kslack = self.slack(k);
                            if kslack <= 0 {
                                // edge k has zero slack => it is allowable
                                self.allowedge[k] = true
                            }
                        }
                        if self.allowedge[k] {
                            if self.label[self.inblossom[w]] == 0 {
                                // (C1) w is a free vertex;
                                // label w with T and label its mate with S (R12).
                                self.assign_label(w, 2, p ^ 1);
                            } else if self.label[self.inblossom[w]] == 1 {
                                // (C2) w is an S-vertex (not in the same blossom);
                                // follow back-links to discover either an
                                // augmenting path or a new blossom.
                                let base = self.scan_blossom(v, w);
                                if base != SENTINEL {
                                    // Found a new blossom; add it to the blossom
                                    // bookkeeping and turn it into an S-blossom.
                                    self.add_blossom(base, k);
                                } else {
                                    // Found an augmenting path; augment the
                                    // matching and end this stage.
                                    self.augment_matching(k);
                                    augmented = true;
                                    break;
                                }
                            } else if self.label[w] == 0 {
                                // w is inside a T-blossom, but w itself has not
                                // yet been reached from outside the blossom;
                                // mark it as reached (we need this to relabel
                                // during T-blossom expansion).
                                assert!(self.label[self.inblossom[w]] == 2);
                                self.label[w] = 2;
                                self.labelend[w] = p ^ 1;
                            }
                        } else if self.label[self.inblossom[w]] == 1 {
                            // keep track of the least-slack non-allowable edge to
                            // a different S-blossom.
                            let b = self.inblossom[v];
                            if self.bestedge[b] == SENTINEL || kslack < self.slack(self.bestedge[b]) {
                                self.bestedge[b] = k;
                            }
                        } else if self.label[w] == 0 {
                            // w is a free vertex (or an unreached vertex inside
                            // a T-blossom) but we can not reach it yet;
                            // keep track of the least-slack edge that reaches w.
                            if self.bestedge[w] == SENTINEL || kslack < self.slack(self.bestedge[w]) {
                                self.bestedge[w] = k;
                            }
                        }
                    }
                }

                if augmented {
                    break;
                }

                // There is no augmenting path under these constraints;
                // compute delta and reduce slack in the optimization problem.
                // (Note that our vertex dual variables, edge slacks and delta's
                // are pre-multiplied by two.)
                let mut deltatype = -1;
                let mut delta = 0;
                let mut deltaedge = 0;
                let mut deltablossom = 0;

                // Verify data structures for delta2/delta3 computation.
                if CHECK_DELTA {
                    self.check_delta2();
                    self.check_delta3();
                }
                if !self.maxcardinality {
                    deltatype = 1;
                    delta = *self.dualvar[0..self.nvertex].iter().min().unwrap();
                }
                // Compute delta2: the minimum slack on any edge between
                // an S-vertex and a free vertex.
                for v in 0..self.nvertex {
                    if (self.label[self.inblossom[v]] == 0) && (self.bestedge[v] != SENTINEL) {
                        let d = self.slack(self.bestedge[v]);
                        if (deltatype == -1) || (d < delta) {
                            delta = d;
                            deltatype = 2;
                            deltaedge = self.bestedge[v];
                        }
                    }
                }

                // Compute delta3: half the minimum slack on any edge between
                // a pair of S-blossoms.
                for b in 0..2*self.nvertex {
                    if (self.blossomparent[b] == SENTINEL) 
                       && (self.label[b] == 1)
                       && (self.bestedge[b] != SENTINEL) {
                        let kslack = self.slack(self.bestedge[b]);
                        let d = kslack / 2;
                        if (deltatype == -1) || (d < delta) {
                            delta = d;
                            deltatype = 3;
                            deltaedge = self.bestedge[b];
                        }
                    }
                }

                // Compute delta4: minimum z variable of any T-blossom.
                for b in self.nvertex..2*self.nvertex {
                    if  self.blossombase[b] != SENTINEL 
                    &&  self.blossomparent[b] == SENTINEL 
                    &&  self.label[b] == 2 
                    &&  (deltatype == -1 || self.dualvar[b] < delta) {
                        delta = self.dualvar[b];
                        deltatype = 4;
                        deltablossom = b;
                    }
                }

                if deltatype == -1 {
                    // No further improvement possible; max-cardinality optimum
                    // reached. Do a final delta update to make the optimum
                    // verifyable.
                    assert!(self.maxcardinality);
                    deltatype = 1;
                    delta = max(0, *(self.dualvar[..self.nvertex]).iter().min().unwrap());
                }

                // Update dual variables according to delta.
                for v in 0..self.nvertex {
                    //println!("{} {} {}", v, self.inblossom[v], self.label[self.inblossom[v]]);
                    match self.label[self.inblossom[v]] {
                        0 => {}
                        1 => {self.dualvar[v] -= delta;} // S-vertex: 2*u = 2*u - 2*delta
                        2 => {self.dualvar[v] += delta;} // T-vertex: 2*u = 2*u + 2*delta
                        _ => {panic!("Unexpected label[inblossom]")}
                    }
                }
                for b in self.nvertex..2*self.nvertex {
                    if (self.blossombase[b] != SENTINEL) && (self.blossomparent[b] == SENTINEL) {
                        match self.label[b] {
                            0 => {}
                            1 => {self.dualvar[b] += delta;} // top-level S-blossom: z = z + 2*delta
                            2 => {self.dualvar[b] -= delta;} // top-level T-blossom: z = z - 2*delta
                            _ => {panic!("Unexpected label")}
                        }
                    }
                }

                // Take action at the point where minimum delta occurred.
                match deltatype {
                    1 => {break;} // No further improvement possible; optimum reached.
                    2 => {  // Use the least-slack edge to continue the search.
                            let (mut i, j, _wt) = self.edges[deltaedge];
                            self.allowedge[deltaedge] = true;
                            if self.label[self.inblossom[i]] == 0 {
                                i = j;
                            }
                            assert!(self.label[self.inblossom[i]] == 1);
                            self.queue.push(i);
                         }
                    3 => {  // Use the least-slack edge to continue the search.
                            self.allowedge[deltaedge] = true;
                            let (i, _j, _wt) = self.edges[deltaedge];
                            assert!(self.label[self.inblossom[i]] == 1);
                            self.queue.push(i);
                         }
                    4 => { // Expand the least-z blossom.
                           self.expand_blossom(deltablossom, false);
                         }
                    _ => {panic!("Unexpected deltatype")}
                }
                // End of a this substage.
            }

            // Stop when no more augmenting path can be found.
            if !augmented {
                break;
            }

            // End of a stage; expand all S-blossoms which have dualvar = 0.
            for b in self.nvertex..2*self.nvertex {
                if  self.blossomparent[b] == SENTINEL 
                  &&  self.blossombase[b] != SENTINEL 
                  &&  self.label[b] == 1 
                  &&  self.dualvar[b] == 0 {
                    self.expand_blossom(b, true);
                }
            }
        }
        // Verify that we reached the optimum solution.
        if CHECK_OPTIMUM {
            self.verify_optimum();
        }

        // Transform mate[] such that mate[v] is the vertex to which v is paired.
        for v in 0..self.nvertex {
            if self.mate[v] != SENTINEL {
                self.mate[v] = self.endpoint[self.mate[v]];
            }
        }
        for v in 0..self.nvertex {
            assert!(self.mate[v] == SENTINEL || self.mate[self.mate[v]] == v);
        }

        self.mate.clone()
    }
    pub fn max_cardinality(&mut self) -> &mut Self {
        self.maxcardinality = true;
        self
    }
}

/// shifts back of vec to front
/// this implements the python code
/// v = v[split:] + v[:split]
fn rotate(v: &mut Vertices, split: usize) {
    let v2 = v.clone();
    let (a, b) = v2.split_at(split);
    v[..b.len()].copy_from_slice(b);
    v[b.len() ..].copy_from_slice(a);
}

/// index into vector using both positive and negative indices (Python-style)
fn pos_neg_index(v: &Vertices, index: i32) -> Vertex {
    let actual_index = if index>= 0 {index as usize} else {(v.len()-(-index) as usize)};
    v[actual_index]
}


#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn no_edges() {
        assert!(Matching::new(vec![]).solve() == vec![]);
    }

     #[test]
    fn single_edge() {
        assert!(Matching::new(vec![(0,1,1)]).solve() == vec![1, 0]);
    }

    #[test]
    fn multiple_edges() {
        assert!(Matching::new(vec![(1,2,10), (2,3,11)]).solve() == vec![SENTINEL, SENTINEL, 3, 2]);
    }

    #[test]
    fn not_max_cardinality() {
        assert!(Matching::new(vec![(1,2,5), (2,3,11), (3,4,5)]).solve() == vec![SENTINEL, SENTINEL, 3, 2, SENTINEL]);
    }

    #[test]
    fn test_max_cardinality() {
        assert!(Matching::new(vec![(1,2,5), (2,3,11), (3,4,5)]).max_cardinality().solve() == vec![SENTINEL, 2, 1, 4, 3]);
    }

    #[test]
    fn negative_weights() {
        assert!(Matching::new(vec![(1,2,2), (1,3,-2), (2,3,1), (2,4,-1), (3,4,-6) ]).solve() == vec![SENTINEL, 2, 1, SENTINEL, SENTINEL]);
        assert!(Matching::new(vec![(1,2,2), (1,3,-2), (2,3,1), (2,4,-1), (3,4,-6) ]).max_cardinality().solve() == vec![SENTINEL, 3, 4, 1, 2]);
    }

    #[test]
    /// create S-blossom and use it for augmentation
    fn s_augmentation() {
        assert!(Matching::new(vec![(1,2,8), (1,3,9), (2,3,10), (3,4,7)]).solve() == vec![SENTINEL, 2, 1, 4, 3]);
        assert!(Matching::new(vec![(1,2,8), (1,3,9), (2,3,10), (3,4,7), (1,6,5), (4,5,6)]).solve() == vec![SENTINEL, 6, 3, 2, 5, 4, 1]);
    }

    #[test]
    /// create S-blossom, relabel as T-blossom, use for augmentation
    fn s_t_relabel_augmentation() {
        assert!(Matching::new(vec![(1,2,9), (1,3,8), (2,3,10), (1,4,5), (4,5,4), (1,6,3)]).solve() == vec![SENTINEL, 6, 3, 2, 5, 4, 1]);
        assert!(Matching::new(vec![(1,2,9), (1,3,8), (2,3,10), (1,4,5), (4,5,3), (1,6,4)]).solve() == vec![SENTINEL, 6, 3, 2, 5, 4, 1]);
        assert!(Matching::new(vec![(1,2,9), (1,3,8), (2,3,10), (1,4,5), (4,5,3), (3,6,4)]).solve() == vec![SENTINEL, 2, 1, 6, 5, 4, 3]);
    }

    #[test]
    /// create nested S-blossom, use for augmentation
    fn s_nested_augmentation() {
        assert!(Matching::new(vec![(1,2,9), (1,3,9), (2,3,10), (2,4,8), (3,5,8), (4,5,10), (5,6,6)]).solve() == vec![SENTINEL, 3, 4, 1, 2, 6, 5]);
    }

    #[test]
    /// create S-blossom, relabel as S, include in nested S-blossom
    fn s_relabel_nested() {
        assert!(Matching::new(vec![(1,2,10), (1,7,10), (2,3,12), (3,4,20), (3,5,20), (4,5,25), (5,6,10), (6,7,10), (7,8,8)]).solve() == vec![SENTINEL, 2, 1, 4, 3, 6, 5, 8, 7]);
    }

    #[test]
    /// create nested S-blossom, augment, expand recursively
    fn s_nested_expand_recursively() {
        assert!(Matching::new(vec![(1,2,8), (1,3,8), (2,3,10), (2,4,12), (3,5,12), (4,5,14), (4,6,12), (5,7,12), (6,7,14), (7,8,12)]).solve() == vec![SENTINEL, 2, 1, 5, 6, 3, 4, 8, 7]);
    }

    #[test]
    /// create S-blossom, relabel as T, expand
    fn s_t_expand() {
        assert!(Matching::new(vec![(1,2,23), (1,5,22), (1,6,15), (2,3,25), (3,4,22), (4,5,25), (4,8,14), (5,7,13)]).solve() == vec![SENTINEL, 6, 3, 2, 8, 7, 1, 5, 4 ]);
    }

    #[test]
    /// create nested S-blossom, relabel as T, expand
    fn s_nest_t_expand() {
        assert!(Matching::new(vec![(1,2,19), (1,3,20), (1,8,8), (2,3,25), (2,4,18), (3,5,18), (4,5,13), (4,7,7), (5,6,7)]).solve() == vec![SENTINEL, 8, 3, 2, 7, 6, 5, 4, 1 ]);
    }

    #[test]
    /// create blossom, relabel as T in more than one way, expand, augment
    fn tnasty_expand() {
        assert!(Matching::new(vec![(1,2,45), (1,5,45), (2,3,50), (3,4,45), (4,5,50), (1,6,30), (3,9,35), (4,8,35), (5,7,26), (9,10,5)]).solve() == vec![SENTINEL, 6, 3, 2, 8, 7, 1, 5, 4, 10, 9 ]);
    }

    #[test]
    /// again but slightly different
    fn tnasty2_expand() {
        assert!(Matching::new(vec![(1,2,45), (1,5,45), (2,3,50), (3,4,45), (4,5,50), (1,6,30), (3,9,35), (4,8,26), (5,7,40), (9,10,5)]).solve() == vec![SENTINEL, 6, 3, 2, 8, 7, 1, 5, 4, 10, 9 ]);
    }

    #[test]
    /// create blossom, relabel as T, expand such that a new least-slack S-to-free edge is produced, augment
    fn t_expand_leastslack() {
        assert!(Matching::new(vec![(1,2,45), (1,5,45), (2,3,50), (3,4,45), (4,5,50), (1,6,30), (3,9,35), (4,8,28), (5,7,26), (9,10,5)]).solve() == vec![SENTINEL, 6, 3, 2, 8, 7, 1, 5, 4, 10, 9 ]);
    }

    #[test]
    /// create nested blossom, relabel as T in more than one way, expand outer blossom such that inner blossom ends up on an augmenting path
    fn nest_tnasty_expand() {
        assert!(Matching::new(vec![(1,2,45), (1,7,45), (2,3,50), (3,4,45), (4,5,95), (4,6,94), (5,6,94), (6,7,50), (1,8,30), (3,11,35), (5,9,36), (7,10,26), (11,12,5)]).solve() == vec![SENTINEL, 8, 3, 2, 6, 9, 4, 10, 1, 5, 7, 12, 11]);
    }

    #[test]
    /// create nested S-blossom, relabel as S, expand recursively
    fn nest_relabel_expand() {
        assert!(Matching::new(vec![(1,2,40), (1,3,40), (2,3,60), (2,4,55), (3,5,55), (4,5,50), (1,8,15), (5,7,30), (7,6,10), (8,10,10), (4,9,30)]).solve() == vec![SENTINEL, 2, 1, 5, 9, 3, 7, 6, 10, 4, 8 ]);
    }
}
