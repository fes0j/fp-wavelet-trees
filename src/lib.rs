use bio::data_structures::rank_select::RankSelect;
use bv::BitVec;
use bv::BitsMut;
use itertools::Itertools;

pub struct WaveletTree {
    root_node: WaveletTreeNode,
    alphabet: Vec<char>,
}

impl WaveletTree {
    pub fn new(string: &str) -> Option<WaveletTree> {
        //Get distinct characters from string  
        let alphabet: Vec<char> = string.chars().unique().collect();
        //Create tree
        //TEMP signature of WaveletTreeNode::new may change (string: Vec<char> -> &str) and (alphabet: Vec<char> -> &[char])
        let string_vec = string.chars().collect();
        if let Some(root_node) = WaveletTreeNode::new(string_vec, alphabet.clone()){
            Some(WaveletTree{root_node, alphabet})
        }else{
            None
        }
    }

    pub fn deserialize(placeholder: &str) {
        //deserialize
    }

    pub fn serialize(&self) {
        //serialize
    }

    pub fn access(&self, position: u32) {
        //resolve character at position
    }

    pub fn select(&self, character: char, n: u32) {
        //return position of n-th character
    }

    pub fn rank(&self, character: char, n: u32) {
        //number of characters until position n
    }
}

struct WaveletTreeNode {
    bit_vec: RankSelect,
    left_child: Box<Option<WaveletTreeNode>>,
    right_child: Box<Option<WaveletTreeNode>>,
}

impl WaveletTreeNode {
    fn new(string: Vec<char>, alphabet: Vec<char>) -> Option<WaveletTreeNode> {
        //split alphabet
        //create bitmap of string lenth
        //assign bitmap 0/1s and create substrings
        //create rankselect structure
        //recusivley create left/right child from substring and partial alphabet
        None
    }
    fn select(&self, position: u32, alphabet: Vec<char>) -> char {
        //switch on 0/1
        //newpos=rank 0/1
        //split alphabet
        //recursivley select(newpos,left/right-alphabet
        'a'
    }
}

#[cfg(test)]
mod tests {

    //RankSelect can use different k for the superblocks
    static SUPERBLOCK_SIZE: usize = 1;

    use super::*;

    //TODO: write tests


    //Test with 2 letters

    #[test]
    fn test_new() {
        let test_string = "ab";
        let w_tree = WaveletTree::new(test_string);

//        let mut bits: BitVec<u8> = BitVec::new_fill(false, 2);
//        bits.set_bit(0, false);
//        bits.set_bit(1, true);
//
//
//        let alphabet = vec!['a', 'b'];
//        let rs =  RankSelect::new(bits,SUPERBLOCK_SIZE );
//        let wavelet_tree_node = WaveletTreeNode { bit_vec: rs, left_child: Box::new(None) ,right_child: Box::new(None)};
//        let wavelet_tree = WaveletTree{alphabet: vec!['a', 'b'],root_node:  wavelet_tree_node};


        assert_eq!( w_tree.alphabet, vec!['a', 'b']);
    }

}
