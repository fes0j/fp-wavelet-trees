use rs_graph::*;
use bv::BitVec;
use bio::data_structures::rank_select::RankSelect;
use crate::WaveletTree;
use crate::wavelet_tree_pointer_based::*;
use core::borrow::Borrow;

pub trait GraphWithWT {
    fn new ( ) -> Self;
    fn neighbor(&self, node: u64, nth_neighbor: u64  )-> Option<u64>;
    fn reverse_neigbor (&self, node: u64, nth_neighbor: u64  )-> Option<u64>;
}

pub struct WaveletTreeGraph {
    bitmap : RankSelect,
    list : u8,
    wavelet_tree: WaveletTreePointer<u64>,
}

impl GraphWithWT for WaveletTreeGraph{
    fn new() -> Self {
        unimplemented!()
    }

    fn neighbor(&self, node: u64, nth_neighbor: u64) -> Option<u64> {
        let l = self.bitmap.select(node);
        if l.is_none() {
            None
        }
        self.wavelet_tree.borrow().access(l.unwrap() + nth_neighbor - node)
    }

    fn reverse_neigbor(&self, node: u64, nth_neighbor: u64) -> Option<u64> {
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use rs_graph::*;
    use rs_graph::traits::Directed;
    use super::*;


    #[test]
    fn test_new() {
        use super::*;

        // fill example graph with directional edges
        let mut g = LinkedListGraph::<u32>::default();
        let nodes = g.add_nodes(6);
        g.add_edge(nodes[0], nodes[1]);
        g.add_edge(nodes[0], nodes[3]);
        g.add_edge(nodes[1], nodes[0]);
        g.add_edge(nodes[1], nodes[2]);
        g.add_edge(nodes[1], nodes[3]);
        g.add_edge(nodes[3], nodes[2]);
        g.add_edge(nodes[4], nodes[0]);
        g.add_edge(nodes[4], nodes[3]);

        //example use of outgoing edges
        g.outedges(nodes[0]).for_each(|(_e, n)| println!("{:?}", n));

        g.add_edge(nodes[3], nodes[2]);


    }

    /// Test if the wavelet-tree graph presents all correct neighbors
    #[test]
    fn test_neighbors() {
        // fill example graph with directional edges
        let mut g = LinkedListGraph::<u64>::default();
        let nodes = g.add_nodes(6);
        g.add_edge(nodes[0], nodes[1]);
        g.add_edge(nodes[0], nodes[3]);
        g.add_edge(nodes[1], nodes[0]);
        g.add_edge(nodes[1], nodes[2]);
        g.add_edge(nodes[1], nodes[3]);
        g.add_edge(nodes[3], nodes[2]);
        g.add_edge(nodes[4], nodes[0]);
        g.add_edge(nodes[4], nodes[3]);

        let w_graph = WaveletTreeGraph::new();
        assert_eq!(2, w_graph.neighbor(0, 1));


    }
}