use bio::data_structures::rank_select::RankSelect;
use bv::BitVec;
use bv::BitsMut;
use itertools::Itertools;

#[derive(PartialEq)]
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
        if let Some(root_node) = WaveletTreeNode::new(string_vec, &alphabet) {
            Some(WaveletTree {
                root_node,
                alphabet,
            })
        } else {
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
    fn new(string: Vec<char>, alphabet: &Vec<char>) -> Option<WaveletTreeNode> {
        if alphabet.len() > 2 {
            //split alphabet
            let string_length = string.len();
            let (l_a, r_a) = alphabet.split_at(alphabet.len() / 2);
            let mut left_alphabet = l_a.to_vec();
            let mut right_alphabet = r_a.to_vec();
            //create bitmap of string lenth
            let mut bitvector: BitVec<u8> = BitVec::with_capacity(string_length as u64);
            let mut left_string: Vec<char> = Vec::new();
            let mut right_string: Vec<char> = Vec::new();
            for i in (0..string_length) {
                //assign bitmap 0/1s
                let c = string.get(i).unwrap();
                let bl = r_a.contains(c);
                bitvector.set_bit(i as u64, bl);
                //fill partial strings
                if bl {
                    right_string.push(*c);
                } else {
                    left_string.push(*c);
                }
            }
            //create rankselect structure
            let rs = RankSelect::new(bitvector, 1);
            Some(WaveletTreeNode {
                bit_vec: rs,
                //recusivley create left/right child from substring and partial alphabet
                left_child: Box::new(WaveletTreeNode::new(left_string, &left_alphabet)),
                right_child: Box::new(WaveletTreeNode::new(right_string, &right_alphabet)),
            })
        } else {
            None
        }
    }
    fn select(&self, position: u32, alphabet: Vec<char>) -> char {
        //switch on 0/1
        //newpos=rank 0/1
        //split alphabet
        //recursivley select(newpos,left/right-alphabet
        'a'
    }
}
impl PartialEq for WaveletTreeNode {
    fn eq(&self, other: &WaveletTreeNode) -> bool {
        self.bit_vec.bits() == other.bit_vec.bits()
            && self.left_child == other.left_child
            && self.right_child == other.right_child
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

        let mut bits: BitVec<u8> = BitVec::new_fill(false, 2);
        bits.set_bit(0, false);
        bits.set_bit(1, true);

        let alphabet = vec!['a', 'b'];
        let rs = RankSelect::new(bits, SUPERBLOCK_SIZE);
        let wavelet_tree_node = WaveletTreeNode {
            bit_vec: rs,
            left_child: Box::new(None),
            right_child: Box::new(None),
        };
        let wavelet_tree = WaveletTree {
            alphabet: vec!['a', 'b'],
            root_node: wavelet_tree_node,
        };

        assert_eq!(w_tree.unwrap(), wavelet_tree);
    }

}
