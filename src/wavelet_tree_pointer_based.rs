use crate::WaveletTree;
use bio::data_structures::rank_select::RankSelect;
use bv::BitVec;
use itertools::Itertools;
use serde::{Deserialize, Serialize};
use std::fmt;

/// A WaveletTree with Pointers is represented here
#[derive(Serialize, Deserialize, PartialEq, Debug)]
pub struct WaveletTreePointer<T: PartialEq + Copy> {
    /// The WaveletTree uses a secondary struct which is recursive
    root_node: Box<WaveletTreeNode>,
    /// Only on this top level the alphabet will be saved
    alphabet: Vec<T>,
}

//This will be the tree structure itself, with the bit vector as data
#[derive(Serialize, Deserialize)]
struct WaveletTreeNode {
    bit_vec: RankSelect,
    left_child: Option<Box<WaveletTreeNode>>,
    right_child: Option<Box<WaveletTreeNode>>,
}

impl WaveletTreeNode {
    fn new<T: PartialEq + Copy>(
        input_string: Vec<T>,
        alphabet: &[T],
    ) -> Option<Box<WaveletTreeNode>> {
        // When the alphabet only consists of two symbols, no new child nodes are needed.
        // The resulting data would only consist of zeros
        if alphabet.len() >= 2 {
            //split alphabet
            let (left_alphabet, right_alphabet) = alphabet.split_at(alphabet.len() / 2);

            //fill partial strings
            let left_string: Vec<T> = input_string
                .clone()
                .into_iter()
                .filter(|c| left_alphabet.contains(c))
                .collect();
            let right_string: Vec<T> = input_string
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
            let rs = RankSelect::new(bitvector, super::SUPERBLOCK_SIZE);
            //recusivley create left/right child from substring and partial alphabet
            let left_child = WaveletTreeNode::new(left_string, left_alphabet);
            let right_child = WaveletTreeNode::new(right_string, right_alphabet);
            Some(Box::new(WaveletTreeNode {
                bit_vec: rs,
                left_child,
                right_child,
            }))
        } else {
            //edge case of an empty or single char string is handled in WaveletTree::new
            None
        }
    }

    fn access<T: PartialEq + Copy>(&self, position: u64, alphabet: &[T]) -> Option<T> {
        //output: object at position index
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
        //proceed left or right
        if self.bit_vec.bits()[position] == false {
            //object from left alphabet
            if let Some(ref lc) = self.left_child {
                //if there is a child go there
                let num = self.bit_vec.rank_0(position).unwrap();
                lc.access(num - 1, &left_alphabet)
            } else {
                Some(left_alphabet[0])
            } //end of recursion
        } else {
            //object from right alphabet
            //access right child
            if let Some(ref rc) = self.right_child {
                //if there is a child go there
                let num = self.bit_vec.rank_1(position).unwrap();
                rc.access(num - 1, &right_alphabet)
            } else {
                Some(right_alphabet[0])
            } //end of recursion
        }
    }

    /// Returns the number of occurences of a character in the sequence until position n
    pub fn rank<T: PartialEq + Copy>(&self, alphabet: &[T], object: T, n: u64) -> Option<u64> {
        //Determine in which half of the alphabet the character is
        let (left_alphabet, right_alphabet) = alphabet.split_at(alphabet.len() / 2);
        if left_alphabet.contains(&object) {
            //already at leaf level
            if left_alphabet.len() == 1 {
                self.bit_vec.rank_0(n)
            } else {
                if let Some(ref lc) = self.left_child {
                    //recursive rank from the leave
                    let rank_left = match self.bit_vec.rank_0(n) {
                        None => None,
                        //node does not contain alphabet up to n
                        Some(0) => Some(0),
                        Some(i) => lc.rank(left_alphabet, object, i - 1),
                    };
                    rank_left
                } else {
                    panic!("rank: There should be a left child but there isn't!");
                }
            }
        } else if right_alphabet.contains(&object) {
            //already at leaf level
            if right_alphabet.len() == 1 {
                self.bit_vec.rank_1(n)
            } else {
                if let Some(ref rc) = self.right_child {
                    //recursive rank from the leave
                    let rank_right = match self.bit_vec.rank_1(n) {
                        None => None,
                        //node does not contain alphabet up to n
                        Some(0) => Some(0),
                        Some(i) => rc.rank(right_alphabet, object, i - 1),
                    };
                    rank_right
                } else {
                    panic!("There should be a right child but there isn't!");
                }
            }
        } else {
            //Character is not in alphabet
            None
        }
    }

    fn select<T: PartialEq + Copy>(&self, character: T, n: u64, alphabet: &[T]) -> Option<u64> {
        //output: position of nth character
        //split alphabet
        let (left_alphabet, right_alphabet) = alphabet.split_at(alphabet.len() / 2);
        //if left alphabet contains character
        if left_alphabet.contains(&character) {
            if let Some(ref lc) = self.left_child {
                //if there is a child go there
                match lc.select(character, n, left_alphabet) {
                    //position of the nth character in the left child
                    //+1 because recursive step returned an index while the #of occurences is needed
                    Some(x) => self.bit_vec.select_0(x + 1),
                    None => None,
                }
            } else {
                //there was no child, look for 0s
                self.bit_vec.select_0(n)
            }
        } else if right_alphabet.contains(&character) {
            if let Some(ref rc) = self.right_child {
                //if there is a child go there
                match rc.select(character, n, right_alphabet) {
                    //position of the nth character in the left child
                    //+1 because recursive step returned an index while the #of occurences is needed
                    Some(x) => self.bit_vec.select_1(x + 1),
                    None => None,
                }
            } else {
                //there was no child, look for 1s
                self.bit_vec.select_1(n)
            }
        } else {
            //Character is not in alphabet
            None
        }
    }
}

impl<T: PartialEq + Copy> WaveletTree<T> for WaveletTreePointer<T> {
    /// Returns a WavletTree using pointer
    ///
    /// # Arguments
    ///
    /// * `iterator` Iterator over any objects implementing PartialEq and Copy traits
    ///
    /// # Example
    ///
    /// ```
    /// use fp_wavelet_trees::wavelet_tree_pointer_based::WaveletTreePointer as WTP;
    /// let wTree:WTP<char> = fp_wavelet_trees::WaveletTree::new("example".chars());
    /// ```
    fn new(iterator: impl Iterator<Item = T>) -> WaveletTreePointer<T> {
        WaveletTreePointer::from_vec(iterator.collect())
    }

    fn access(&self, position: u64) -> Option<T> {
        self.root_node.access(position, &self.alphabet[..])
    }

    /// Return position of n-th character
    fn select(&self, object: T, n: u64) -> Option<u64> {
        self.root_node.select(object, n, &self.alphabet[..])
    }

    fn rank(&self, object: T, n: u64) -> Option<u64> {
        self.root_node.rank(&self.alphabet[..], object, n)
    }
}

impl<T: PartialEq + Copy> WaveletTreePointer<T> {
    fn from_vec(vector: Vec<T>) -> WaveletTreePointer<T> {
        //Get distinct characters from string
        let mut alphabet = Vec::new();
        for v in vector.clone() {
            if !alphabet.contains(&v) {
                alphabet.push(v);
            }
        }

        //edge case of an empty or single char string
        if alphabet.len() < 2 {
            return WaveletTreePointer {
                root_node: {
                    let mut bitvector = BitVec::new();
                    bitvector.resize(vector.len() as u64, true);
                    Box::new(WaveletTreeNode {
                        bit_vec: RankSelect::new(bitvector, super::SUPERBLOCK_SIZE),
                        left_child: None,
                        right_child: None,
                    })
                },
                alphabet,
            };
        }
        //Create tree
        let root_node =
            WaveletTreeNode::new(vector, &alphabet) /* even with an empty string, there should be a node */
                .expect("Without a tree node the WaveletTree will be useless ");

        WaveletTreePointer {
            root_node,
            alphabet,
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

impl From<String> for WaveletTreePointer<char> {
    fn from(input: String) -> Self {
        WaveletTreePointer::new(input.chars())
    }
}

impl From<&str> for WaveletTreePointer<char> {
    fn from(input: &str) -> Self {
        WaveletTreePointer::new(input.chars())
    }
}

impl<T: PartialEq + Copy> From<Vec<T>> for WaveletTreePointer<T> {
    fn from(input: Vec<T>) -> Self {
        WaveletTreePointer::from_vec(input)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::WaveletTree;
    use bv::BitVec;
    use bv::BitsMut;
    use unicode_segmentation::UnicodeSegmentation;

    /// # Test with two different letters
    /// This will test for alphabet and child nodes.
    /// The RankSelect Vector will also be tested.
    ///
    #[test]
    fn test_2_letter_tree() {
        let two_tree: WaveletTreePointer<char> = WaveletTreePointer::new("ab".chars());
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
        let five_tree: WaveletTreePointer<char> = WaveletTreePointer::new(input_string.chars());
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

    //test for basic creation
    #[test]
    fn test_7_letter_tree() {
        let string: Vec<char> = "abcdefg".chars().collect();
        let seven_tree: WaveletTreePointer<char> = WaveletTreePointer::new(string.into_iter());
        // let alphabet: Vec<char> = input_string.chars().unique().collect();

        // assert_eq!(seven_tree.alphabet, alphabet);
        assert!(seven_tree.root_node.left_child.is_some());
        assert!(seven_tree.root_node.right_child.is_some());
        let lc = seven_tree.root_node.left_child.unwrap();
        let rc = seven_tree.root_node.right_child.unwrap();
        assert!(lc.left_child.is_none());
        assert!(lc.right_child.is_some());
        assert!(rc.left_child.is_some());
        assert!(rc.right_child.is_some());
        let left_right = BitVec::from_bits(&[false, true]);
        assert_eq!(*lc.right_child.unwrap().bit_vec.bits(), left_right);
    }

    /// Testing tests
    #[test]
    fn test_new() {
        let test_string = "ab".chars();
        let w_tree = WaveletTreePointer::new(test_string);

        let mut bits: BitVec<u8> = BitVec::new_fill(false, 2);
        bits.set_bit(0, false);
        bits.set_bit(1, true);

        let rs = RankSelect::new(bits, crate::SUPERBLOCK_SIZE);
        let wavelet_tree_node = Box::new(WaveletTreeNode {
            bit_vec: rs,
            left_child: None,
            right_child: None,
        });
        let wavelet_tree = WaveletTreePointer {
            alphabet: vec!['a', 'b'],
            root_node: wavelet_tree_node,
        };

        assert_eq!(w_tree, wavelet_tree);
    }

    #[test]
    fn test_access_empty() {
        let w_tree = WaveletTreePointer::new("".chars());

        assert_eq!(None, w_tree.access(0));
    }

    /// Test if a one letter tree shows the correct number
    #[test]
    fn test_access_1_letter() {
        let test_string: Vec<char> = "a".chars().collect();
        let w_tree = WaveletTreePointer::new("a".chars());

        assert_eq!(test_string[0], w_tree.access(0).unwrap());
        assert_eq!(None, w_tree.access(1));
    }

    #[test]
    fn test_access_7_letter() {
        let test_string: Vec<char> = "abcdefg".chars().collect();
        let w_tree = WaveletTreePointer::new(test_string.clone().into_iter());

        assert_eq!(test_string[0], w_tree.access(0).unwrap());
        assert_eq!(test_string[1], w_tree.access(1).unwrap());
        assert_eq!(test_string[2], w_tree.access(2).unwrap());
        assert_eq!(test_string[4], w_tree.access(4).unwrap());
        assert_eq!(test_string[6], w_tree.access(6).unwrap());
        assert_eq!(None, w_tree.access(7));
    }

    /// Simple Test for select
    #[test]
    fn test_select_basic() {
        let test_string = "cabdacdbabadcab";
        let w_tree = WaveletTreePointer::new(test_string.clone().chars());

        assert_eq!(w_tree.select('c', 2), Some(5));
    }

    //Test for a character outside the alphabet
    #[test]
    fn test_select_outside_alphabet() {
        let test_string = "cabdacdbabadcab";
        let w_tree = WaveletTreePointer::new(test_string.clone().chars());
        assert_eq!(w_tree.select('f', 2), None);
    }

    //Test for index out of bounds
    #[test]
    fn test_select_out_of_bounds() {
        let test_string = "cabdacdbabadcab";
        let w_tree = WaveletTreePointer::new(test_string.clone().chars());

        assert_eq!(w_tree.select('c', 4), None);
    }

    #[test]
    fn test_serialize_deserialize() {
        let test_string = "cbacbcbcbbcabcabcabcabbca";
        let w_tree = WaveletTreePointer::new(test_string.clone().chars());

        let serialized = serde_json::to_string(&w_tree).unwrap();
        let w_tree2: WaveletTreePointer<char> = serde_json::from_str(&serialized).unwrap();

        assert_eq!(w_tree, w_tree2)
    }

    #[test]
    fn test_select_5_letter() {
        let test_string = "abcde";
        let w_tree = WaveletTreePointer::new(test_string.clone().chars());

        assert_eq!(w_tree.select('a', 1), Some(0));
        assert_eq!(w_tree.select('b', 1), Some(1));
        assert_eq!(w_tree.select('c', 1), Some(2));
        assert_eq!(w_tree.select('d', 1), Some(3));
        assert_eq!(w_tree.select('e', 1), Some(4));
    }

    #[test]
    fn test_select_2_letter() {
        let test_string = "ab";
        let w_tree = WaveletTreePointer::new(test_string.clone().chars());

        assert_eq!(w_tree.select('a', 1), Some(0));
        assert_eq!(w_tree.select('b', 1), Some(1));
        assert_eq!(w_tree.select('c', 1), None);
        assert_eq!(w_tree.select('a', 2), None);
        assert_eq!(w_tree.select('b', 3), None);
    }

    #[test]
    fn test_rank_2_letters() {
        //let test_string = "aaaaaaaaaabsbsbdsbdsabb";
        let test_string = "ababababababab";
        let w_tree = WaveletTreePointer::new(test_string.clone().chars());

        assert_eq!(w_tree.rank('a', 0), Some(1));
        assert_eq!(w_tree.rank('b', 0), Some(0));

        assert_eq!(w_tree.rank('a', 6), Some(4));
        assert_eq!(w_tree.rank('b', 6), Some(3));

        assert_eq!(w_tree.rank('a', 13), Some(7));
        assert_eq!(w_tree.rank('b', 13), Some(7));

        assert_eq!(w_tree.rank('b', 17), None);

        assert_eq!(w_tree.rank('c', 5), None);
    }

    #[test]
    fn test_rank_5_letter() {
        let test_string = "abcde";
        let w_tree = WaveletTreePointer::new(test_string.clone().chars());

        assert_eq!(w_tree.rank('a', 0), Some(1));
        assert_eq!(w_tree.rank('b', 1), Some(1));
        assert_eq!(w_tree.rank('c', 2), Some(1));
        assert_eq!(w_tree.rank('d', 3), Some(1));
        assert_eq!(w_tree.rank('e', 4), Some(1));
    }

    #[test]
    fn test_rank_unicode() {
        let test_string = "Hello world, こんにちは世界, Привет, мир";
        let test_string = UnicodeSegmentation::graphemes(test_string, true).collect::<Vec<&str>>();
        let w_tree: WaveletTreePointer<&str> = WaveletTree::new(test_string.into_iter());

        //println!("{:#?}", w_tree);
        assert_eq!(w_tree.rank("o", 4), Some(1));
        assert_eq!(w_tree.rank("世", 32), Some(1));
        assert_eq!(w_tree.rank("и", 32), Some(2));

        assert_eq!(w_tree.rank("o", 16), Some(2));
        assert_eq!(w_tree.rank("世", 16), Some(0));
        assert_eq!(w_tree.rank("и", 16), Some(0));

        assert_eq!(w_tree.rank("o", 0), Some(0));
        assert_eq!(w_tree.rank("世", 0), Some(0));
        assert_eq!(w_tree.rank("и", 0), Some(0));

        assert_eq!(w_tree.rank("木", 32), None);
    }
}
