#![feature(rustc_private)]

use std::time::{Instant};
extern crate rand;
use rand::Rng;

extern crate mwmatching;
use mwmatching::{Edges, Weight, Vertex, Matching};

const N:Vertex = 2000;

fn main() {
    let mut edges:Edges = vec![];
    for i in 0..N-1 {
        for j in i+1..N {
            let wt: Weight = rand::thread_rng().gen_range(-50,50);
            edges.push((i, j, wt));
        }
    }
    let now = Instant::now();
    let _results = Matching::new(edges).solve();
    println!("Elapsed time: {:?}", now.elapsed());
}
