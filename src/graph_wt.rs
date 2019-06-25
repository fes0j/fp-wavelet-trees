use crate::wavelet_tree_pointer_based::*;
use crate::WaveletTree;
use bio::data_structures::rank_select::RankSelect;
use bv::BitVec;

pub trait GraphWithWT {
    // Creates an empty WaveletTreeGraph with 'size' nodes
    fn new(size: usize) -> Self;
    // Adds an edge from startnode to endnode
    // does nothing (or panics?) if the WaveletTree is already created?
    fn add_edge(&mut self, startnode: u64, endnode: u64) -> Result<(), &'static str>;
    // Creates the bitmap and the WaveletTree from the underlying list (if not done yet)
    // returns the 'nth_neighbor' of the 'node' or None if there is None
    fn neighbor(&mut self, node: u64, nth_neighbor: u64) -> Option<u64>;
    // Creates the bitmap and the WaveletTree from the underlying list (if not done yet)
    // returns the 'nth_reverse_neighbor' of the 'node' or None if there is None
    fn reverse_neigbor(&mut self, node: u64, nth_reverse_neighbor: u64) -> Option<u64>;
}

pub struct WaveletTreeGraph {
    bit_vec: Vec<bool>,
    bitmap: Option<RankSelect>,
    list: Vec<u64>,
    wavelet_tree: Option<WaveletTreePointer<u64>>,
    size: usize,
}

impl GraphWithWT for WaveletTreeGraph {
    fn new(size: usize) -> Self {
        WaveletTreeGraph {
            // fill the bit_vec with as much 'ones' as there are graph nodes
            bit_vec: vec![true; size],
            bitmap: None,
            list: vec![],
            wavelet_tree: None,
            size: size,
        }
    }

    fn add_edge(&mut self, startnode: u64, endnode: u64) -> Result<(), &'static str> {
        // check if wavelet_tree wasn't created already
        if self.wavelet_tree == None {
            if self.size < (startnode + 1) as usize {
                return Err("startnode not found in graph");
            }
            if self.size < (endnode + 1) as usize {
                return Err("endnode not found in graph");
            }
            // contains the index of the (startnode+1)-th '1' in the bit_vec
            let upper_insert_bound = select(&self.bit_vec, startnode + 1);
            if upper_insert_bound != None {
                self.bit_vec
                    .insert((upper_insert_bound.unwrap()) as usize, false);
                self.list.insert(
                    (upper_insert_bound.unwrap() - startnode - 1) as usize,
                    endnode,
                );
            }
            // this is the case if the startnode is the last node
            else {
                self.bit_vec.push(false);
                self.list.push(endnode);
            }
            return Ok(());
        }
        Err("Graph already created, cannot further add edges")
    }

    fn neighbor(&mut self, node: u64, nth_neighbor: u64) -> Option<u64> {
        if self.wavelet_tree == None {
            self.bitmap = Some(bool_vec_to_rankselect(&self.bit_vec));
            self.wavelet_tree = Some(WaveletTreePointer::new(self.list.clone().into_iter()));
        }
        let l = self.bitmap.as_mut().unwrap().select(node + 1);
        if l.is_none() {
            return None;
        }

        let c = self.bitmap.as_mut().unwrap().select(node + 2);
        if c.is_none() {
            return None;
        }

        // The node 'node' has less neighbors than 'nth_neighbor'
        if l.unwrap() >= c.unwrap() - nth_neighbor {
            return None;
        }
        // The node 'node' has no neighbor
        if self.bitmap.as_mut().unwrap().rank_1(l.unwrap() + 1) > Some(node + 1) {
            return None;
        }
        self.wavelet_tree
            .as_mut()
            .unwrap()
            .access(l.unwrap() + nth_neighbor - (node + 1))
    }

    fn reverse_neigbor(&mut self, node: u64, nth_reverse_neighbor: u64) -> Option<u64> {
        if self.wavelet_tree == None {
            self.bitmap = Some(bool_vec_to_rankselect(&self.bit_vec));
            self.wavelet_tree = Some(WaveletTreePointer::new(self.list.clone().into_iter()));
        }
        // get the index of the 'nth_reverse_neighbor' of 'node' in the adjacency list
        let p = self
            .wavelet_tree
            .as_mut()
            .unwrap()
            .select(node, nth_reverse_neighbor);
        if p != None {
            // get the index of the 'nth_reverse_neighbor' in the bitmap
            let index_in_bitmap = self.bitmap.as_mut().unwrap().select_0(p.unwrap() + 1);
            if index_in_bitmap != None {
                // get the startnode of the edge to the 'node' (this ist the reverse neigbor)
                let result = self.bitmap.as_mut().unwrap().rank(index_in_bitmap.unwrap());
                if result != None {
                    return Some(result.unwrap() - 1);
                }
                return None;
            }
            index_in_bitmap
        } else {
            p
        }
    }
}

fn select(bit_vec: &Vec<bool>, n: u64) -> Option<u64> {
    let mut i = 0;
    let mut counter = 0;
    loop {
        if i >= bit_vec.len() {
            return None;
        }
        if bit_vec[i] == true {
            if counter == n {
                return Some(i as u64);
            }
            counter += 1;
        }
        i += 1;
    }
}

fn bool_vec_to_rankselect(bit_vec: &Vec<bool>) -> RankSelect {
    let mut bits: BitVec<u8> = BitVec::new();
    for b in bit_vec {
        bits.push(*b);
    }
    RankSelect::new(bits, 1)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn create_sample_graph() -> WaveletTreeGraph {
        let mut graph = WaveletTreeGraph::new(6);
        graph.add_edge(0, 1).expect("Could not add edge to graph");
        graph.add_edge(0, 3).expect("Could not add edge to graph");
        graph.add_edge(1, 0).expect("Could not add edge to graph");
        graph.add_edge(1, 3).expect("Could not add edge to graph");
        graph.add_edge(1, 2).expect("Could not add edge to graph");
        graph.add_edge(3, 2).expect("Could not add edge to graph");
        graph.add_edge(4, 0).expect("Could not add edge to graph");
        graph.add_edge(4, 3).expect("Could not add edge to graph");
        graph
    }

    #[test]
    fn test_add_edge() {
        let graph = create_sample_graph();

        assert_eq!(graph.list, vec![1, 3, 0, 3, 2, 2, 0, 3]);
        assert_eq!(
            graph.bit_vec,
            vec![
                true, false, false, true, false, false, false, true, true, false, true, false,
                false, true
            ]
        );
    }

    #[test]
    fn test_neighbor() {
        let mut graph = create_sample_graph();

        assert_eq!(None, graph.neighbor(0, 3));
        assert_eq!(Some(3), graph.neighbor(0, 2));
        assert_eq!(Some(1), graph.neighbor(0, 1));

        assert_eq!(None, graph.neighbor(1, 4));
        assert_eq!(Some(2), graph.neighbor(1, 3));
        assert_eq!(Some(3), graph.neighbor(1, 2));
        assert_eq!(Some(0), graph.neighbor(1, 1));

        assert_eq!(None, graph.neighbor(2, 0));

        assert_eq!(None, graph.neighbor(3, 2));
        assert_eq!(Some(2), graph.neighbor(3, 1));

        assert_eq!(None, graph.neighbor(4, 3));
        assert_eq!(Some(3), graph.neighbor(4, 2));
        assert_eq!(Some(0), graph.neighbor(4, 1));

        assert_eq!(None, graph.neighbor(5, 1));
    }

    #[test]
    fn test_reverse_neighbor() {
        let mut graph = create_sample_graph();

        // Reverse neigbors of node 0
        assert_eq!(Some(1), graph.reverse_neigbor(0, 1));
        assert_eq!(Some(4), graph.reverse_neigbor(0, 2));

        // Reverse neigbors of node 1
        assert_eq!(Some(0), graph.reverse_neigbor(1, 1));

        // Reverse neigbors of node 2
        assert_eq!(Some(1), graph.reverse_neigbor(2, 1));
        assert_eq!(Some(3), graph.reverse_neigbor(2, 2));

        // Reverse neigbors of node 3
        assert_eq!(Some(0), graph.reverse_neigbor(3, 1));
        assert_eq!(Some(1), graph.reverse_neigbor(3, 2));
        assert_eq!(Some(4), graph.reverse_neigbor(3, 3));

        // Reverse neigbors of node 4
        assert_eq!(None, graph.reverse_neigbor(4, 1));

        // Reverse neigbors of node 5
        assert_eq!(None, graph.reverse_neigbor(5, 1));
    }
}
