use bio::data_structures::rank_select::RankSelect;
use bv::BitVec;
use bv::Bits;
use bv::BitsExt;
use bv::BitsMut;
use itertools::Itertools;
use serde::{Deserialize, Serialize};
use std::fmt;

use crate::WaveletTree;
use std::fmt::Debug;

#[derive(Serialize, Deserialize)]
pub struct WaveletTreeCompact<T: PartialEq + Copy> {
    alphabet: Vec<T>,
    bit_vec: RankSelect,
    sequence_len: u64,
}

impl<T: PartialEq + Copy> WaveletTree<T> for WaveletTreeCompact<T> {
    fn new(vector: impl Iterator<Item = T>) -> Self {
        WaveletTreeCompact::new(vector.collect())
    }

    fn access(&self, position: u64) -> Option<T> {
        //Check if position is valid
        if position >= self.sequence_len {
            None
        } else {
            self.access_helper(position, &self.alphabet[..], 0, self.sequence_len - 1)
        }
    }

    fn select(&self, object: T, n: u64) -> Option<u64> {
        self.select_intern(&self.alphabet[..], object, n, 0, self.sequence_len - 1)
    }

    fn rank(&self, object: T, n: u64) -> Option<u64> {
        self.rank_intern(&self.alphabet[..], object, n, 0, self.sequence_len - 1)
    }
}

impl<T: PartialEq + Copy> WaveletTreeCompact<T> {
    pub fn new(input: Vec<T>) -> WaveletTreeCompact<T> {
        let sequence_len = input.len() as u64;
        //Create alphabet
        let mut alphabet: Vec<T> = Vec::new();
        input.iter().foreach(|x| {
            if !alphabet.contains(&x) {
                alphabet.push(*x);
            }
        });

        //Create vector for levels
        let mut levels: Vec<BitVec<u8>> = Vec::new();

        //Create bitvecs for levels
        if alphabet.len() == 1 {
            let mut local_bitvec = BitVec::new();
            input.iter().foreach(|x| {
                local_bitvec.push(false);
            });
            levels.push(local_bitvec);
        } else {
            WaveletTreeCompact::create_bitvec(0, &mut levels, &input[..], &alphabet[..]);
        }

        //Append all the levels into one big bitvec
        let mut bit_vec: BitVec<u8> = BitVec::new();
        for l in levels {
            //every layer starts at a multiple of sequence length so layers in betwene must be filled up
            let filler: BitVec<u8> = match l.len() {
                0 => BitVec::new(),
                x => BitVec::new_fill(false, sequence_len - (x as u64)),
            };
            bit_vec = bit_vec.bit_concat(l).to_bit_vec();
            bit_vec = bit_vec.bit_concat(filler).to_bit_vec();
        }

        WaveletTreeCompact {
            alphabet: alphabet.to_owned(),

            bit_vec: RankSelect::new(bit_vec, crate::SUPERBLOCK_SIZE),
            sequence_len,
        }
    }

    fn create_bitvec(level: usize, levels: &mut Vec<BitVec<u8>>, sequence: &[T], alphabet: &[T]) {
        if alphabet.len() >= 2 {
            //Split alphabet

            let (left_alphabet, right_alphabet) = WaveletTreeCompact::splitalphabet(alphabet);

            let mut l_seq = Vec::new();
            let mut r_seq = Vec::new();
            let mut local_bitvec = BitVec::new();

            //Fill left/right sequence and create bitvector for local "node"
            sequence.iter().for_each(|x| {
                if left_alphabet.contains(x) {
                    l_seq.push(*x);
                    local_bitvec.push(false);
                } else {
                    r_seq.push(*x);
                    local_bitvec.push(true);
                }
            });

            //Append to level bitvec
            if !levels.len() > level {
                //Create new for this level
                levels.push(BitVec::new());
            }

            levels[level] = levels[level].bit_concat(local_bitvec).to_bit_vec();

            //Call recursively for childs
            WaveletTreeCompact::create_bitvec(level + 1, levels, &l_seq[..], left_alphabet); //Left needs to be first!!
            WaveletTreeCompact::create_bitvec(level + 1, levels, &r_seq[..], right_alphabet);
        }
    }

    fn rank_0(&self, l: u64, r: u64) -> Option<u64> {
        //include the start index
        let offset = match self.bit_vec.bits()[l] {
            true => Some(0),
            false => Some(1),
        };
        Some(self.bit_vec.rank_0(r)? - self.bit_vec.rank_0(l)? + offset?)
    }

    fn rank_1(&self, l: u64, r: u64) -> Option<u64> {
        //include the start index
        let offset = match self.bit_vec.bits()[l] {
            true => Some(1),
            false => Some(0),
        };
        Some(self.bit_vec.rank_1(r)? - self.bit_vec.rank_1(l)? + offset?)
    }

    fn select_0(&self, l: u64, r: u64, n: u64) -> Option<u64> {
        //rank_0 of l-1
        let offset = match self.bit_vec.bits()[l] {
            true => 0,
            false => 1,
        };
        let rank_lm1 = self.bit_vec.rank_0(l).unwrap() - offset;
        //rank_lm1 0s appear before so +idex will be in the current node or right
        let index = self.bit_vec.select_0(n + rank_lm1);
        //only return if index remains in the node
        match index {
            None => None,
            Some(i) => {
                if i <= r && i >= l {
                    Some(i - l)
                } else {
                    None
                }
            }
        }
    }

    fn select_1(&self, l: u64, r: u64, n: u64) -> Option<u64> {
        //rank_1 of l-1
        let offset = match self.bit_vec.bits()[l] {
            true => 1,
            false => 0,
        };
        let rank_lm1 = self.bit_vec.rank_1(l).unwrap() - offset;
        //rank_lm1 1s appear before so +idex will be in the current node or right
        let index = self.bit_vec.select_1(n + rank_lm1);
        //only return if index remains in the node
        match index {
            None => None,
            Some(i) => {
                if i <= r && i >= l {
                    Some(i - l)
                } else {
                    None
                }
            }
        }
    }

    fn splitalphabet<'a>(alphabet: &'a [T]) -> (&[T], &[T]) {
        if alphabet.len() == 0 {
            panic!("can not split empty alphabet")
        } else if alphabet.len() == 1 {
            (alphabet, &[])
        } else {
            alphabet.split_at(2usize.pow(((alphabet.len()) as f64).log2().ceil() as u32 - 1))
        }
    }

    fn rank_intern(
        &self,
        alphabet: &[T],
        object: T,
        index: u64,
        left: u64,
        right: u64,
    ) -> Option<u64> {
        //Split alphabet
        let (left_alphabet, right_alphabet) = WaveletTreeCompact::splitalphabet(alphabet);
        if left_alphabet.contains(&object) {
            if left_alphabet.len() == 1 {
                //need to account for the left most bit itselfe but can not rely on left>0
                self.rank_0(left, left + index)
            } else {
                if let Some(w) = self.rank_0(left, right) {
                    //in case there is a child,determin boundries
                    let left_child_left = left + self.sequence_len;
                    let left_child_right = left_child_left + w - 1;
                    let right_child_left = left_child_right + 1;
                    let right_child_right = right + self.sequence_len;
                    let pos_in_child = self.rank_0(left, left + index);
                    match pos_in_child {
                        None => None,
                        Some(0) => Some(0),
                        Some(i) => self.rank_intern(
                            left_alphabet,
                            object,
                            i - 1,
                            left_child_left,
                            left_child_right,
                        ),
                    }
                } else {
                    //out of bounds
                    panic!("rank: no child in tree");
                }
            }
        } else if right_alphabet.contains(&object) {
            if right_alphabet.len() == 1 {
                //need to account for the left most bit itselfe but can not rely on left>0
                self.rank_1(left, left + index)
            } else {
                if let Some(w) = self.rank_0(left, right) {
                    //in case there is a child,determin boundries
                    let left_child_left = left + self.sequence_len;
                    let left_child_right = left_child_left + w - 1;
                    let right_child_left = left_child_right + 1;
                    let right_child_right = right + self.sequence_len;
                    let pos_in_child = self.rank_1(left, left + index);
                    match pos_in_child {
                        None => None,
                        Some(0) => Some(0),
                        Some(i) => self.rank_intern(
                            right_alphabet,
                            object,
                            i - 1,
                            right_child_left,
                            right_child_right,
                        ),
                    }
                } else {
                    //out of bounds
                    panic!("rank: no child in tree");
                }
            }
        } else {
            None
        }
    }

    fn select_intern(
        &self,
        alphabet: &[T],
        object: T,
        index: u64,
        left: u64,
        right: u64,
    ) -> Option<u64> {
        //Split alphabet
        let (left_alphabet, right_alphabet) = WaveletTreeCompact::splitalphabet(alphabet);
        if left_alphabet.contains(&object) {
            if left_alphabet.len() == 1 {
                self.select_0(left, right, index)
            } else {
                if let Some(w) = self.rank_0(left, right) {
                    //in case there is a child,determin boundries
                    let left_child_left = left + self.sequence_len;
                    let left_child_right = left_child_left + w - 1;
                    let right_child_left = left_child_right + 1;
                    let right_child_right = right + self.sequence_len;

                    //position of the nth character in the left child
                    match self.select_intern(
                        left_alphabet,
                        object,
                        index,
                        left_child_left,
                        left_child_right,
                    ) {
                        //+1 because recursive step returned an index while the #of occurences is needed
                        Some(x) => self.select_0(left, right, x + 1),
                        None => None,
                    }
                } else {
                    //out of bounds
                    panic!("rank: no child in tree");
                }
            }
        } else if right_alphabet.contains(&object) {
            if right_alphabet.len() == 1 {
                //panic!("l{} r{} i{}",left,right,index);
                self.select_1(left, right, index)
            } else {
                if let Some(w) = self.rank_0(left, right) {
                    //in case there is a child,determin boundries
                    let left_child_left = left + self.sequence_len;
                    let left_child_right = left_child_left + w - 1;
                    let right_child_left = left_child_right + 1;
                    let right_child_right = right + self.sequence_len;

                    //position of the nth character in the right child
                    match self.select_intern(
                        right_alphabet,
                        object,
                        index,
                        right_child_left,
                        right_child_right,
                    ) {
                        //+1 because recursive step returned an index while the #of occurences is needed
                        Some(x) => self.select_1(left, right, x + 1),
                        None => None,
                    }
                } else {
                    //out of bounds
                    panic!("rank: no child in tree");
                }
            }
        } else {
            None
        }
    }

    fn access_helper(&self, position: u64, alphabet: &[T], l: u64, r: u64) -> Option<T> {
        //println!("A l:{}, r:{} pos:{} pos+l{}", l, r, position, position+l);
        if alphabet.len() <= 1 {
            return Some(alphabet[0]);
        }

        if l == r { //Reached end
            //return Some(alphabet[0])
            return None;
        }

        //println!("access pos:{}, alp:{:?} l:{}, r:{} vec[pos]:{} pos:{}", position, alphabet, l, r, self.bit_vec.get(l + position), l+position);

        assert!(l <= r);

        let (left_alphabet, right_alphabet) = WaveletTreeCompact::splitalphabet(alphabet);
        let pos_rank = self.rank_0(l, r)?;
        if self.bit_vec.get(l + position) {
            //Right child
            //let child_l = self.sequence_len + l + self.rank_0(l, r).unwrap() - 1;
            //let child_r = self.sequence_len + r;
            let child_l = self.sequence_len + pos_rank + l;
            let child_r = self.sequence_len + r;

            let mut position = self.rank_1(l, l + position)?;
            self.access_helper(position - 1, right_alphabet, child_l, child_r)
        } else {
            //Left child
            //let child_l = self.sequence_len + l;
            //let child_r = self.sequence_len + l + self.rank_0(l, r).unwrap() - 2;
            let child_l = self.sequence_len + l;
            let child_r = child_l + pos_rank - 1;

            let mut position = self.rank_0(l, l + position)?;
            self.access_helper(position - 1, left_alphabet, child_l, child_r)
        }
    }
}

impl<T: PartialEq + Copy + Debug> Debug for WaveletTreeCompact<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "WaveletTreeCompact {{ alphabet:{:?} bv:{:?}}}",
            self.alphabet,
            self.bit_vec.bits()
        )
    }
}

impl<T: PartialEq + Copy> PartialEq for WaveletTreeCompact<T> {
    fn eq(&self, other: &Self) -> bool {
        self.alphabet == other.alphabet && self.bit_vec.bits() == other.bit_vec.bits()
    }

    fn ne(&self, other: &Self) -> bool {
        !self.eq(other)
    }
}

impl From<String> for WaveletTreeCompact<char>{
    fn from(input: String) -> Self {
        WaveletTreeCompact::new(input.chars().collect())
    }
}

impl From<&str> for WaveletTreeCompact<char> {
    fn from(input: &str) -> Self {
        WaveletTreeCompact::new(input.chars().collect())
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use unicode_segmentation::UnicodeSegmentation;

    #[test]
    fn test_new() {
        let w_tree = WaveletTreeCompact::new("alabar_a_la_alabarda".chars().collect());

        println!("{:?}", w_tree);
    }

    #[test]
    fn test_new_split_alphabet() {
        let alphabet: Vec<char> = "abcde".chars().collect();
        let (l, r) = WaveletTreeCompact::splitalphabet(&alphabet[..]);

        assert!(alphabet.len() == 5);
        assert_eq!(l.len(), 4);
        assert_eq!(r.len(), 1);

        let test_string = "abcde".chars().collect();
        let mut w_tree = WaveletTreeCompact::new(test_string);

        assert_eq!(w_tree.bit_vec.bits()[0], false); //a
        assert_eq!(w_tree.bit_vec.bits()[1], false); //b
        assert_eq!(w_tree.bit_vec.bits()[2], false); //c
        assert_eq!(w_tree.bit_vec.bits()[3], false); //d
        assert_eq!(w_tree.bit_vec.bits()[4], true); //e

        assert_eq!(w_tree.bit_vec.bits()[5], false); //a
        assert_eq!(w_tree.bit_vec.bits()[6], false); //b
        assert_eq!(w_tree.bit_vec.bits()[7], true); //c
        assert_eq!(w_tree.bit_vec.bits()[8], true); //d
        assert_eq!(w_tree.bit_vec.bits()[9], false); //placeholder

        assert_eq!(w_tree.bit_vec.bits()[10], false); //a
        assert_eq!(w_tree.bit_vec.bits()[11], true); //b
        assert_eq!(w_tree.bit_vec.bits()[12], false); //c
        assert_eq!(w_tree.bit_vec.bits()[13], true); //d
        assert_eq!(w_tree.bit_vec.bits()[14], false); //placeholder
    }

    #[test]
    fn test_rank_edge_cases() {
        let one_element = WaveletTreeCompact::new("a".chars().collect());
        assert_eq!(one_element.rank('a', 0), Some(1));
        assert_eq!(one_element.rank('a', 1), None);
        assert_eq!(one_element.rank('b', 0), None);
    }

    #[test]
    fn test_rank_select_0_1() {
        let test_string = "abcde".chars().collect();
        let mut w_tree = WaveletTreeCompact::new(test_string); //00001 00110

        assert_eq!(w_tree.rank_0(0, 3), Some(4));
        assert_eq!(w_tree.rank_0(0, 4), Some(4));
        assert_eq!(w_tree.rank_0(4, 5), Some(1));
        assert_eq!(w_tree.rank_0(4, 4), Some(0));
        assert_eq!(w_tree.rank_0(3, 3), Some(1));
        assert_eq!(w_tree.rank_1(0, 3), Some(0));
        assert_eq!(w_tree.rank_1(4, 5), Some(1));

        assert_eq!(w_tree.select_0(0, 3, 2), Some(1));
        assert_eq!(w_tree.select_0(3, 5, 2), Some(2));
        assert_eq!(w_tree.select_0(7, 8, 1), None);
        assert_eq!(w_tree.select_1(7, 8, 1), Some(0));
        assert_eq!(w_tree.select_1(2, 5, 3), None);
    }

    #[test]
    fn test_rank_5_letter() {
        let test_string = "abcde".chars().collect();
        let mut w_tree = WaveletTreeCompact::new(test_string);
        assert_eq!(w_tree.bit_vec.bits().len(), 15);
        assert_eq!(w_tree.rank('a', 0), Some(1));
        assert_eq!(w_tree.rank('b', 1), Some(1));
        assert_eq!(w_tree.rank('c', 2), Some(1));
        assert_eq!(w_tree.rank('d', 3), Some(1));
        assert_eq!(w_tree.rank('e', 4), Some(1));
    }

    #[test]
    fn test_rank_long_sequence_letters() {
        let test_string = "aaaaabbbbbcde".chars().collect();
        let mut w_tree = WaveletTreeCompact::new(test_string);

        assert_eq!(w_tree.rank('a', 0), Some(1));
        assert_eq!(w_tree.rank('a', 1), Some(2));
        assert_eq!(w_tree.rank('a', 2), Some(3));
        assert_eq!(w_tree.rank('a', 3), Some(4));
        assert_eq!(w_tree.rank('a', 4), Some(5));
        assert_eq!(w_tree.rank('a', 5), Some(5));
        assert_eq!(w_tree.rank('a', 6), Some(5));
        assert_eq!(w_tree.rank('a', 7), Some(5));
    }

    #[test]
    fn test_rank_unicode() {
        let test_string = "Hello world, こんにちは世界, Привет, мир";
        let test_string = UnicodeSegmentation::graphemes(test_string, true).collect::<Vec<&str>>();
        let mut w_tree: WaveletTreeCompact<&str> = WaveletTreeCompact::new(test_string);

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

    #[test]
    fn test_new_pointer_free() {
        let w_tree = WaveletTreeCompact::from("alabar_a_la_alabarda");

        //TODO compare it to expected value
        assert_eq!(w_tree, w_tree);
        //TEMP just for debug purposes
        println!("{:?}", w_tree);
    }

    #[test]
    fn test_access_unicode_string() {
        let test_string = "Hello world, こんにちは世界, Привет, мир";
        let w_tree = WaveletTreeCompact::from(test_string);

        //println!("{:?}", w_tree);

        for (i, c) in test_string.chars().enumerate() {
            assert_eq!(w_tree.access(i as u64), Some(c));
            //println!("Access: {} Expected: {} Got:{}\n\n", i, c, w_tree.access(i as u64).unwrap());
        }
    }

    #[test]
    fn test_access_invalid_pos(){
        let test_string = "Hello world";
        let w_tree = WaveletTreeCompact::from(test_string);

        assert_eq!(w_tree.access(11), None);
        assert_eq!(w_tree.access(100), None);
    }

    #[test]
    fn test_access_num_vec() {
        let test_vec: Vec<i64> = vec![1,2,3,4,5,6,7,8,9,0,10,5,3,6,3,6,2,7,4,8, -3, -6, -3, -10, -6,2,8,3,7,42,1024, 2048, 1024,3,6,8,3];
        let w_tree = WaveletTreeCompact::new(test_vec.clone());

        //Check if all elements are present
        for (i, c) in test_vec.iter().enumerate() {
            assert_eq!(w_tree.access(i as u64), Some(*c));
        }
    }

    #[test]
    fn test_from_string(){
        let test_string: String = "Test".to_string();
        let w_tree = WaveletTreeCompact::from(test_string.clone());

        //Check if all Elements are present
        for (i, c) in test_string.chars().enumerate() {
            assert_eq!(w_tree.access(i as u64), Some(c));
        }
        //Test that there are no additional elements
        assert_eq!(w_tree.access(test_string.len() as u64), None);
    }

    #[test]
    fn test_select() {
        let test_string = "abcdeb";
        let w_tree = WaveletTreeCompact::from(test_string); //00001 00110 01010

        assert_eq!(w_tree.select('b', 1), Some(1));
        assert_eq!(w_tree.select('b', 2), Some(5));
        assert_eq!(w_tree.select('b', 0), None);
    }
}
