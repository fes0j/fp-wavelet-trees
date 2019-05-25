use bio::data_structures::rank_select::RankSelect;
use bv::BitVec;
use bv::BitsMut;
use itertools::Itertools;
use std::fmt;

///RankSelect can use different k for the superblocks
static SUPERBLOCK_SIZE: usize = 1;

#[derive(PartialEq, Debug)]
pub struct WaveletTree {
    root_node: WaveletTreeNode,
    alphabet: Vec<char>,
}

impl WaveletTree {
    pub fn new(string: &str) -> WaveletTree {
        //Get distinct characters from string
        let alphabet: Vec<char> = string.chars().unique().collect();
        //Create tree
        //TEMP signature of WaveletTreeNode::new may change (string: Vec<char> -> &str) and (alphabet: Vec<char> -> &[char])
        let string_vec = string.chars().collect();
        let root_node =
            WaveletTreeNode::new(string_vec, &alphabet) /* even with an empty string, there should be a node */
                .expect("Without a tree node the WaveletTree will be useless ");

        WaveletTree {
            root_node,
            alphabet,
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

//This will be the tree structure itself, with the bit vector as data
struct WaveletTreeNode {
    bit_vec: RankSelect,
    left_child: Box<Option<WaveletTreeNode>>,
    right_child: Box<Option<WaveletTreeNode>>,
}

impl WaveletTreeNode {
    fn new(string: Vec<char>, alphabet: &Vec<char>) -> Option<WaveletTreeNode> {

        // When the alphabet only consists of two symbols, no new child nodes are needed.
        // The resulting data would only consist of zeros
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
            for i in 0..string_length {
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
            let rs = RankSelect::new(bitvector, SUPERBLOCK_SIZE);
            Some(WaveletTreeNode {
                bit_vec: rs,
                //recusivley create left/right child from substring and partial alphabet
                left_child: Box::new(WaveletTreeNode::new(left_string, &left_alphabet)),
                right_child: Box::new(WaveletTreeNode::new(right_string, &right_alphabet)),
            })
        } else {
            let mut bit_vector: BitVec<u8> = BitVec::with_capacity(string.len() as u64);
            // Split alphabet in half, even tough we are now only interested in one symbol
            let (left_alphabet, right_alphabet) = alphabet.split_at(alphabet.len() / 2);
            // "Map" each char to its place in the bit_vector
            string.iter().foreach(|x| { bit_vector.push(right_alphabet.contains(x)) });
            let rs = RankSelect::new(bit_vector, SUPERBLOCK_SIZE);

            ///create last node, where only the vector is needed
            Some(WaveletTreeNode {
                bit_vec: rs,
                left_child: Box::new(None),
                right_child: Box::new(None),
            })
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

impl fmt::Debug for WaveletTreeNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "WaveletTreeNode {{ bit_vec: {:?}}}", self.bit_vec.bits())
    }
}

#[cfg(test)]
mod tests {
    use super::*;


    /// # Test with two different letters
    /// This will test for alphabet and child nodes.
    /// The RankSelect Vector will also be tested.
    ///
    #[test]
    fn test_2_letter_tree() {
        let two_tree: WaveletTree = WaveletTree::new("ab");
        let alphabet: Vec<char> = "ab".chars().collect();

        assert_eq!(two_tree.alphabet, alphabet);
        assert_eq!(two_tree.root_node.right_child, Box::new(None));
        assert_eq!(two_tree.root_node.left_child, Box::new(None));

        // To Test the bit vector, we create our one (the expected one).
        let mut bits: BitVec<u8> = BitVec::new_fill(false, 2);
        bits.set_bit(0, false);
        bits.set_bit(1, true);

        assert_eq!(*two_tree.root_node.bit_vec.bits(), bits);
    }


    /// Testing tests
    #[test]
    #[ignore]
    fn test_new() {
        let test_string = "abc";
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

        //assert_eq!(w_tree.unwrap(), wavelet_tree);
    }
}
