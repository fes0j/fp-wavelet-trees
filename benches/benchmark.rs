
#[macro_use]
extern crate criterion;
extern crate fp_wavelet_trees;

use criterion::{Criterion, ParameterizedBenchmark, Benchmark};
use criterion::black_box;
use fp_wavelet_trees::{graph_wt, WaveletTree};
use fp_wavelet_trees::graph_wt::*;
use fp_wavelet_trees::wavelet_tree_compact::*;
use fp_wavelet_trees::wavelet_tree_pointer_based::*;
use core::borrow::{BorrowMut, Borrow};


fn graph_bench_point_build(n: usize) {

   let mut wt_graph_builder = WTGraphBuilder::with_capacities(n);
    for i  in 0..(n-2) {
        wt_graph_builder.add_edge(i as u64,(i+1) as u64 );
        wt_graph_builder.add_edge(i as u64,(i+2) as u64 );
    }
    let mut graph = wt_graph_builder.to_graph::<WaveletTreePointer<u64>>();
    graph.neighbor(0,1);
}

fn graph_bench_point<T : WaveletTree<u64>>( graph : &WaveletTreeGraph<T>) {
    for _i in 100..400 {
        graph.neighbor(0, 1);
    }
}
fn graph_bench_reverse<T : WaveletTree<u64>>( graph : &WaveletTreeGraph<T>) {
    for _i in 100..400 {
        graph.reverse_neigbor(0, 1);
    }
}
fn graph_bench_compact(n: usize) {
    let mut wt_graph_builder = WTGraphBuilder::with_capacities(n);
    for i  in 0..(n-2) {
        wt_graph_builder.add_edge(i as u64,(i+1) as u64 );
        wt_graph_builder.add_edge(i as u64,(i+2) as u64 );
    }
    let mut graph = wt_graph_builder.to_graph::<WaveletTreeCompact<u64>>();
    graph.neighbor(0,1);

}

fn bench_graph_build(c: &mut Criterion) {
    c.bench(
        "Graph",
        Benchmark::new("Compact", |b| b.iter(|| graph_bench_compact(400)))
            .with_function("Pointer", |b| b.iter(|| graph_bench_point_build(400))),
    );
}

fn bench_graph_neighbor(c: &mut Criterion) {
    let n : u64 = 500;
    let mut wt_graph_builder = WTGraphBuilder::with_capacities(n as usize);
    for i  in 0..(n-2) {
        wt_graph_builder.add_edge(i as u64,(i+1) as u64 );
        wt_graph_builder.add_edge(i as u64,(i+2) as u64 );
    }
    let graphP = wt_graph_builder.to_graph::<WaveletTreePointer<u64>>();
    let graphC = wt_graph_builder.to_graph::<WaveletTreeCompact<u64>>();

    c.bench(
        "Graph Neighbor",
        Benchmark::new("Pointer", move | b | b.iter(| | graph_bench_point(&graphP )))
            .with_function( "Compact", move | b | b.iter(| | graph_bench_point(&graphC ))),
    );

}

fn bench_graph_reverse_neighbor(c: &mut Criterion) {
    let n: u64 = 500;
    let mut wt_graph_builder = WTGraphBuilder::with_capacities(n as usize);
    for i in 0..(n - 2) {
        wt_graph_builder.add_edge(i as u64, (i + 1) as u64);
        wt_graph_builder.add_edge(i as u64, (i + 2) as u64);
    }
    let graphP = wt_graph_builder.to_graph::<WaveletTreePointer<u64>>();
    let graphC = wt_graph_builder.to_graph::<WaveletTreeCompact<u64>>();
    c.bench(
        "Graph Reverse Neighbor",
        Benchmark::new("Pointer", move |b| b.iter(|| graph_bench_reverse(&graphP)))
            .with_function("Compact", move |b| b.iter(|| graph_bench_reverse(&graphC))),
    );
}


criterion_group!(benches, bench_graph_build, bench_graph_neighbor, bench_graph_reverse_neighbor);
criterion_main!(benches);