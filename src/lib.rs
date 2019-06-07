use bio::data_structures::rank_select::RankSelect;
use bv::BitVec;
use bv::BitsMut;
use itertools::Itertools;
use std::fmt;
use serde::{Serialize, Deserialize};

///RankSelect can use different k for the superblocks
static SUPERBLOCK_SIZE: usize = 1;

#[derive(Serialize, Deserialize, PartialEq, Debug)]
pub struct WaveletTree {
    root_node: Box<WaveletTreeNode>,
    alphabet: Vec<char>,
}

impl WaveletTree {
    pub fn new(string: &str) -> WaveletTree {
        //Get distinct characters from string
        let alphabet: Vec<char> = string.chars().unique().collect();
        //edge case of an empty or single char string
        if alphabet.len() < 2 {
            return WaveletTree {
                root_node: {
                    let mut bitvector = BitVec::new();
                    bitvector.resize(string.len() as u64, true);
                    Box::new(WaveletTreeNode {
                        bit_vec: RankSelect::new(bitvector, SUPERBLOCK_SIZE),
                        left_child: None,
                        right_child: None,
                    })
                },
                alphabet,
            };
        }
        //Create tree
        let root_node =
            WaveletTreeNode::new(string.chars().collect(), &alphabet) /* even with an empty string, there should be a node */
                .expect("Without a tree node the WaveletTree will be useless ");

        WaveletTree {
            root_node,
            alphabet,
        }
    }

    pub fn access(&self, position: u64) -> Option<char> {
        self.root_node.access(position, &self.alphabet[..])
    }

    pub fn select(&mut self, character: char, n: u64) -> Option<u64> {
        self.root_node.select(character,n,&self.alphabet[..])
    }

    pub fn rank(&self, character: char, n: u32) -> Option<u32> {
        //number of characters until position n
        None
    }
}

//This will be the tree structure itself, with the bit vector as data
#[derive(Serialize, Deserialize)]
struct WaveletTreeNode {
    bit_vec: RankSelect,
    left_child: Option<Box<WaveletTreeNode>>,
    right_child: Option<Box<WaveletTreeNode>>,
}

impl WaveletTreeNode {
    fn new(input_string: Vec<char>, alphabet: &[char]) -> Option<Box<WaveletTreeNode>> {
        // When the alphabet only consists of two symbols, no new child nodes are needed.
        // The resulting data would only consist of zeros
        if 2 <= alphabet.len() {
            //split alphabet
            let (left_alphabet, right_alphabet) = alphabet.split_at(alphabet.len() / 2);

            //fill partial strings
            let left_string = input_string
                .clone()
                .into_iter()
                .filter(|c| left_alphabet.contains(c))
                .collect();
            let right_string = input_string
                .clone()
                .into_iter()
                .filter(|c| right_alphabet.contains(c))
                .collect();

            //create bitvector of string length
            let mut bitvector: BitVec<u8> = BitVec::with_capacity(input_string.len() as u64);
            //fill bitvector
            input_string.iter().foreach(|character|
                //assign bitmap 0/1s
                bitvector.push(right_alphabet.contains(&character)));

            //create rankselect structure
            let rs = RankSelect::new(bitvector, SUPERBLOCK_SIZE);
            Some(Box::new(WaveletTreeNode {
                bit_vec: rs,
                //recusivley create left/right child from substring and partial alphabet
                left_child: WaveletTreeNode::new(left_string, &left_alphabet),
                right_child: WaveletTreeNode::new(right_string, &right_alphabet),
            }))
        } else {
            //edge case of an empty or single char string is handleled in WaveletTree::new
            None
        }
    }

    fn access(&self, position: u64, alphabet: &[char]) -> Option<char> {
        //check if position is valid
        if self.bit_vec.bits().len() <= position {
            return None;
        }
        //zero/one char alphabet case
        if alphabet.len() <= 1 {
            return Some(alphabet[0]);
        }
        //split alphabet
        let (left_alphabet, right_alphabet) = alphabet.split_at(alphabet.len() / 2);
        //if length of alphabet is 2 return left/right char
        if alphabet.len() == 2 {
            //switch on 0/1
            match self.bit_vec.bits()[position] {
                false => Some(left_alphabet[0]),
                true => Some(right_alphabet[0]),
            }
        } else {
            //alphabet is longer
            //recursivley access(rank0/1,left/right-alphabet)
            match self.bit_vec.bits()[position] {
                //unwrap must be safe caus position is valid
                false => self.access(self.bit_vec.rank_0(position).unwrap(), &left_alphabet),
                true => self.access(self.bit_vec.rank_1(position).unwrap(), &right_alphabet),
            }
        }
    }

    fn select(&mut self, character: char ,n: u64, alphabet: &[char]) -> Option<u64> {
        //output: position of nth character
        //split alphabet
        let (left_alphabet, right_alphabet) = alphabet.split_at(alphabet.len() / 2);
        //if left alphabet contains character
        if left_alphabet.contains(&character) {
            if left_alphabet.len()==1 {
                self.bit_vec.select_0(n)
            }else{
                //take the child out of the option
                let lc = self.left_child.take();
                let mut lc =lc.unwrap();
                //posinchild is the position of the nth character in the left child
                let pos_in_child = lc.select(character,n,left_alphabet);
                //put the child back in to the option
                let _ignore=self.left_child.replace(lc);
                //pos in current is the position of the nth character in the current node
                match pos_in_child{//+1 because recursive step returned an index while the #of occurences is needed
                    Some(x) => self.bit_vec.select_0(x+1),
                    None => None
                }
            }
        }else if right_alphabet.contains(&character){
            if right_alphabet.len()==1 {
                self.bit_vec.select_1(n)
            }else{
                //take the child out of the option
                let rc = self.right_child.take();
                let mut rc = rc.unwrap();
                //posinchild is the position of the nth character in the left child
                let pos_in_child = rc.select(character,n,right_alphabet);
                //put the child back in to the option
                let _ignore=self.right_child.replace(rc);
                //pos in current is the position of the nth character in the current node
                match pos_in_child{//+1 because recursive step returned an index while the #of occurences is needed
                    Some(x) => self.bit_vec.select_1(x+1),
                    None => None
                }
            }
        }else{None}
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
        write!(
            f,
            "WaveletTreeNode {{ {:?}, r:{:?} l:{:?} }}",
            self.bit_vec.bits(),
            self.left_child,
            self.right_child
        )
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
        assert_eq!(two_tree.root_node.right_child, None);
        assert_eq!(two_tree.root_node.left_child, None);

        // To Test the bit vector, we create our one (the expected one).
        let mut bits: BitVec<u8> = BitVec::new_fill(false, 2);
        bits.set_bit(0, false);
        bits.set_bit(1, true);

        assert_eq!(*two_tree.root_node.bit_vec.bits(), bits);
    }

    /// # Test with five letters
    /// This will test alphabet and child nodes.
    /// The RankSelect Vector will also be tested.
    ///
    #[test]
    fn test_5_letter_tree() {
        let input_string = "abcda";
        let five_tree: WaveletTree = WaveletTree::new(input_string);
        let alphabet: Vec<char> = input_string.chars().unique().collect();

        assert_eq!(five_tree.alphabet, alphabet);

        // To Test the bit vector, we create our one (the expected one).
        let mut bits: BitVec<u8> = BitVec::new_fill(false, 5);
        //Now set the remaining bits
        bits.set_bit(2, true);
        bits.set_bit(3, true);

        assert_eq!(*five_tree.root_node.bit_vec.bits(), bits);

        // Test if the left node has the correct data for aba
        let left_child = five_tree.root_node.left_child.unwrap();
        let left_child_bits = BitVec::from_bits(&[false, true, false]);
        assert_eq!(*left_child.bit_vec.bits(), left_child_bits);

        // Test if the right node has the correct data for cd
        let right_child = five_tree.root_node.right_child.unwrap();
        let right_child_bits = BitVec::from_bits(&[false, true]);
        assert_eq!(*right_child.bit_vec.bits(), right_child_bits);
    }

    /// Testing tests
    #[test]
    fn test_new() {
        let test_string = "ab";
        let w_tree = WaveletTree::new(test_string);

        let mut bits: BitVec<u8> = BitVec::new_fill(false, 2);
        bits.set_bit(0, false);
        bits.set_bit(1, true);

        let alphabet = vec!['a', 'b'];
        let rs = RankSelect::new(bits, SUPERBLOCK_SIZE);
        let wavelet_tree_node = Box::new(WaveletTreeNode {
            bit_vec: rs,
            left_child: None,
            right_child: None,
        });
        let wavelet_tree = WaveletTree {
            alphabet: vec!['a', 'b'],
            root_node: wavelet_tree_node,
        };

        assert_eq!(w_tree, wavelet_tree);
    }

    #[test]
    fn test_access_empty() {
        let test_string = "";
        let w_tree = WaveletTree::new(test_string);

        assert_eq!(test_string.chars().nth(0), w_tree.access(0));
    }

    #[test]
    fn test_access_1_letter() {
        let test_string = "a";
        let w_tree = WaveletTree::new(test_string);

        assert_eq!(test_string.chars().nth(0), w_tree.access(0));
        assert_eq!(test_string.chars().nth(1), w_tree.access(1));
    }

    #[test]
    fn test_access_5_letter() {
        let test_string = "abcde";
        let w_tree = WaveletTree::new(test_string);

        assert_eq!(test_string.chars().nth(0), w_tree.access(0));
        assert_eq!(test_string.chars().nth(2), w_tree.access(2));
        assert_eq!(test_string.chars().nth(4), w_tree.access(4));
        assert_eq!(test_string.chars().nth(5), w_tree.access(5));
    }
    
    //Simple Test for select
    #[test]
    fn test_select_basic(){
        let test_string = "cabdacdbabadcab";
        let mut w_tree = WaveletTree::new(test_string);
        
        assert_eq!(w_tree.select('c',2),Some(5));
    }
    
    //Test for a character outside the alphabet
    #[test]
    fn test_select_outside_alphabet(){
        let test_string = "cabdacdbabadcab";
        let mut w_tree = WaveletTree::new(test_string);
        assert_eq!(w_tree.select('f',2),None);
    }
    
    //Test for index out of bounds
    #[test]
    fn test_select_out_of_bounds(){
        let test_string = "cabdacdbabadcab";
        let mut w_tree = WaveletTree::new(test_string);
        
        assert_eq!(w_tree.select('c',4),None);
    }

    #[test]
    fn test_serialize_deserialize() {
        let test_string = "cbacbcbcbbcabcabcabcabbca";
        let w_tree = WaveletTree::new(test_string);

        let serialized = serde_json::to_string(&w_tree).unwrap();
        let w_tree2: WaveletTree = serde_json::from_str(&serialized).unwrap();

        assert_eq!(w_tree, w_tree2)
    }
}
