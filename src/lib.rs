use bio::data_structures::rank_select::RankSelect;
use bv::BitVec;
use bv::BitsMut;


pub struct WaveletTree {
    root_node: WaveletTreeNode,
    alphabet: Vec<char>,
}

impl WaveletTree {
    pub fn new(placeholder: &str) {
        //new tree from parameter
    }
    pub fn deserialize(placeholder: &str) {
        //deserialize
    }
    pub fn serialize(&self) {
        //serialize
    }
    pub fn access(position: u32) {
        //resolve character at position
    }
    pub fn select(character: char, n: u32) {
        //return position of n-th character
    }
    pub fn rank(character: char, n: u32) {
        //number of characters until position n
    }
}

struct WaveletTreeNode {
    bit_vec: BitVec<u8>,
    rs: RankSelect,
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
    fn select(position: u32, alphabet: Vec<char>) -> char {
        //switch on 0/1
        //newpos=rank 0/1
        //split alphabet
        //recursivley select(newpos,left/right-alphabet
        'a'
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    //TODO: write tests


    //Test with 4 letters
    #[ignore]
    #[test]
    fn test_deserialize() {
        let test_string = "abacdc";
        let w_tree = WaveletTree {};
        WaveletTree::deserialize(&test_string);
        assert_eq!(0, 0);
    }
}
