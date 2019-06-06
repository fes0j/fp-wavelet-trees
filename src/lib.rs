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
        //edge case of an empty or single char string
        if alphabet.len() < 2 {
            return WaveletTree {
                root_node: {
                    let mut bitvector = BitVec::new();
                    bitvector.resize(string.len() as u64, true);
                    WaveletTreeNode {
                        bit_vec: RankSelect::new(bitvector, SUPERBLOCK_SIZE),
                        left_child: Box::new(None),
                        right_child: Box::new(None),
                    }
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

    pub fn deserialize(placeholder: &str) {
        //deserialize
    }

    pub fn serialize(&self) {
        //serialize
    }

    pub fn access(&self, position: u64) -> Option<char> {
        self.root_node.access(position, &self.alphabet[..])
    }


    pub fn select(&self, character: char, n: u64) -> Option<u64> {
        // check if the character is valid
        if self.alphabet.clone().into_iter().filter(|c| *c == character).count() == 0 {
            return None;
        }

        // contains the path nodes from the root to the leaf with the char 'character'
        let mut path_nodes:Vec<WaveletTreeNode> = vec![self.root_node.clone()];
        // contains the path from the root to the leaf with the char 'character' (either 'l' or 'r')
        let mut path:Vec<char> = vec![];

        let (left_alphabet, right_alphabet) = self.alphabet.split_at(self.alphabet.len() / 2);
        let mut alphabet = if left_alphabet.contains(&character) {
            if left_alphabet.len() >= 2 {
                path_nodes.push(path_nodes.last().unwrap().left_child.clone().unwrap());
                path.push('l');
            }
            left_alphabet
        }
        else {
            if right_alphabet.len() >= 2 {
                path_nodes.push(path_nodes.last().unwrap().right_child.clone().unwrap());
                path.push('r');
            }
            right_alphabet
        };
        while alphabet.len() > 2 {
            let (left_alphabet, right_alphabet) = alphabet.split_at(alphabet.len() / 2);
            alphabet = if left_alphabet.contains(&character) {
                if left_alphabet.len() >= 2 {
                    path_nodes.push(path_nodes.last().unwrap().left_child.clone().unwrap());
                    path.push('l');
                }
                left_alphabet
            }
            else {
                if right_alphabet.len() >= 2 {
                    path_nodes.push(path_nodes.last().unwrap().right_child.clone().unwrap());
                    path.push('r');
                }
                right_alphabet
            };
        }



        let mut i = None;
        let mut node = path_nodes.pop();
        let mut direction = path.pop();
        let (left_alphabet, right_alphabet) = if direction != None {
            alphabet.split_at(alphabet.len() / 2)
        }
        else {
            (left_alphabet,right_alphabet)
        };

        if  node != None {
            if left_alphabet.len() == 0 {
                i = Some(n-1);
            }
            else if left_alphabet.contains(&character) {
                i = node.unwrap().bit_vec.select_0(n);
            }
            else {
                i = node.unwrap().bit_vec.select_1(n);
            }
        }

        node = path_nodes.pop();

        while direction != None && node != None && i != None {
            if direction.unwrap() == 'l' {
                i = node.unwrap().bit_vec.select_0(i.unwrap()+1);
            }
            else {
                i = node.unwrap().bit_vec.select_1(i.unwrap()+1);
            }
            direction = path.pop();
            node = path_nodes.pop();
        }
        // return the value of i as an index [0...]
        i
    }

    pub fn rank(&self, character: char, n: u32) -> Option<u32> {
        //number of characters until position n
        None
    }
}

//This will be the tree structure itself, with the bit vector as data
struct WaveletTreeNode {
    bit_vec: RankSelect,
    left_child: Box<Option<WaveletTreeNode>>,
    right_child: Box<Option<WaveletTreeNode>>,
}

impl WaveletTreeNode {
    fn new(input_string: Vec<char>, alphabet: &[char]) -> Option<WaveletTreeNode> {
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
            Some(WaveletTreeNode {
                bit_vec: rs,
                //recusivley create left/right child from substring and partial alphabet
                left_child: Box::new(WaveletTreeNode::new(left_string, &left_alphabet)),
                right_child: Box::new(WaveletTreeNode::new(right_string, &right_alphabet)),
            })
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
            "WaveletTreeNode {{ {:?}, l:{:?} r:{:?} }}",
            self.bit_vec.bits(),
            self.left_child,
            self.right_child
        )
    }
}

impl Clone for WaveletTreeNode {
    fn clone(&self) -> WaveletTreeNode {
        let bitvector: BitVec<u8> = (*self.bit_vec.bits()).clone();
        let rs = RankSelect::new(bitvector, self.bit_vec.k());
        WaveletTreeNode{
            bit_vec: rs,
            left_child: self.left_child.clone(),
            right_child: self.right_child.clone(),
        }
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
        let wavelet_tree_node = WaveletTreeNode {
            bit_vec: rs,
            left_child: Box::new(None),
            right_child: Box::new(None),
        };
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

    //Test for select if it goes out of bounds or mishandels missing chars
    #[test]
    fn test_select(){
        let test_string = "cabdacdbabadcab";
        let w_tree = WaveletTree::new(test_string);

        assert_eq!(w_tree.select('a',2),Some(4));
        assert_eq!(w_tree.select('a',6),None);
        assert_eq!(w_tree.select('f',2),None);
    }

    #[test]
    fn test_select_5_letter() {
        let test_string = "abcde";
        let w_tree = WaveletTree::new(test_string);

        assert_eq!(w_tree.select('a', 1),Some(0));
        assert_eq!(w_tree.select('b', 1),Some(1));
        assert_eq!(w_tree.select('c', 1),Some(2));
        assert_eq!(w_tree.select('d', 1),Some(3));
        assert_eq!(w_tree.select('e', 1),Some(4));
    }

    #[test]
    fn test_select_2_letter() {
        let test_string = "ab";
        let w_tree = WaveletTree::new(test_string);

        assert_eq!(w_tree.select('a', 1),Some(0));
        assert_eq!(w_tree.select('b', 1),Some(1));
        assert_eq!(w_tree.select('c', 1),None);
        assert_eq!(w_tree.select('a', 2),None);
        assert_eq!(w_tree.select('b', 3),None);
    }
}
