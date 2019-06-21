/// RankSelect can use different k for the superblocks
const SUPERBLOCK_SIZE: usize = 1;

//Submodules
pub mod wavelet_tree_compact;
pub mod wavelet_tree_pointer_based;

/// WaveletTrees
pub trait WaveletTree<T> {
    fn new(vector: impl Iterator<Item = T>) -> Self;
    fn access(&self, position: u64) -> Option<T>;
    fn select(&self, object: T, n: u64) -> Option<u64>;
    fn rank(&self, object: T, n: u64) -> Option<u64>;
}