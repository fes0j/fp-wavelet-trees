use crate::wavelet_tree_pointer_based::*;
use crate::WaveletTree;
use bio::data_structures::rank_select::RankSelect;
use bv::BitVec;
use core::borrow::Borrow;
use rs_graph::*;

pub trait GraphWithWT {
    // Creates an empty WaveletTreeGraph with 'size' nodes
    fn new(size: u64) -> Self;
    // Adds an edge from startnode to endnode
    // does nothing (or panics?) if the WaveletTree is already created?
    fn add_edge(&mut self, startnode: u64, endnode: u64);
    // Creates the bitmap and the WaveletTree from the underlying list (if not done yet)
    // returns the 'nth_neighbor' of the 'node' or None if there is None
    fn neighbor(&mut self, node: u64, nth_neighbor: u64) -> Option<u64>;
    // Creates the bitmap and the WaveletTree from the underlying list (if not done yet)
    // returns the 'nth_reverse_neighbor' of the 'node' or None if there is None
    fn reverse_neigbor(&mut self, node: u64, nth_reverse_neighbor: u64) -> Option<u64>;
}

pub struct WaveletTreeGraph {
    bit_vec: BitVec<u8>,
    bitmap: Option<RankSelect>,
    list: Vec<u64>,
    wavelet_tree: Option<WaveletTreePointer<u64>>,
}

impl GraphWithWT for WaveletTreeGraph {
    fn new(size: u64) -> Self {
        WaveletTreeGraph {
            bit_vec: BitVec::new_fill(true, size),
            bitmap: None,
            list: vec![],
            wavelet_tree: None,
        }
    }

    fn add_edge(&mut self, startnode: u64, endnode: u64) {
        unimplemented!()
    }

    fn neighbor(&mut self, node: u64, nth_neighbor: u64) -> Option<u64> {
        let l = self.bitmap.as_mut().unwrap().select(node);
        if l.is_none() {
            return None;
        }
        self.wavelet_tree
            .as_mut()
            .unwrap()
            .access(l.unwrap() + nth_neighbor - node)
    }

    fn reverse_neigbor(&mut self, node: u64, nth_neighbor: u64) -> Option<u64> {
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rs_graph::traits::Directed;
    use rs_graph::*;

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
