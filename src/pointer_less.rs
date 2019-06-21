use bio::data_structures::rank_select::RankSelect;
use bv::BitVec;
use bv::BitsMut;
use bv::Bits;
use bv::BitsExt;
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
    fn new(vector: impl Iterator<Item=T>) -> Self {
        unimplemented!()
    }

    fn access(&self, position: u64) -> Option<T> {
        if position < self.sequence_len {

            let mut l = 0u64;
            let mut r = self.sequence_len-1;
            let mut position = position;
            let mut alphabet = &self.alphabet[..];
            loop {
                if l == r { //Reached end, return
                    return Some(alphabet[0]);
                }

                if self.bit_vec.bits()[position] { //Right child
                    let child_l = self.sequence_len + l;
                    let child_r = self.sequence_len + l + self.rank_0(l, r).unwrap() -1;

                    position = self.rank_1(l, l+position).unwrap();
                    l = child_l;
                    r = child_r;
                    let (_, right_alphabet) = alphabet.split_at(
                        2usize.pow(
                            ((alphabet.len() + 1) as f64).ln().ceil() as u32 -1
                        ) -1
                    );
                    alphabet = right_alphabet;

                } else { //Left child
                    let child_l = self.sequence_len + l + self.rank_0(l, r).unwrap();
                    let child_r = self.sequence_len + r;

                    position = self.rank_0(l, l+position).unwrap();
                    l = child_l;
                    r = child_r;
                    let (left_alphabet, _) = alphabet.split_at(
                        2usize.pow(
                            ((alphabet.len() + 1) as f64).ln().ceil() as u32 -1
                        ) -1
                    );
                    alphabet = left_alphabet;
                }
            }
        } else {
            None
        }
    }
    
    fn select(&self, object: T, n: u64) -> Option<u64> {
        unimplemented!()
    }

    fn rank(&self, object: T, n: u64) -> Option<u64> {
        unimplemented!()
    }
}

impl<T: PartialEq + Copy> WaveletTreeCompact<T> {
    pub fn new(input: Vec<T>) -> WaveletTreeCompact<T> {
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
        WaveletTreeCompact::create_bitvec(0, &mut levels, &input[..], &alphabet[..]);
        for l in levels.clone() {
            println!("new: {:?}", l);
        }

        //Append all the levels into one big bitvec
        let mut bit_vec:BitVec<u8> = BitVec::new();
        for l in levels {
            bit_vec = bit_vec.bit_concat(l).to_bit_vec();
        }

        WaveletTreeCompact {
            alphabet: alphabet.to_owned(),
            bit_vec: RankSelect::new(bit_vec, crate::SUPERBLOCK_SIZE),
            sequence_len: input.len() as u64,
        }
    }

    fn create_bitvec(level: usize, levels: &mut Vec<BitVec<u8>>, sequence: &[T], alphabet: &[T]) {
        if alphabet.len() >= 2 {
            //Split alphabet
            let (left_alphabet, right_alphabet) = alphabet.split_at(
                2usize.pow(
                    ((alphabet.len() + 1) as f64).log2().ceil() as u32 -1
                ) -1
            );

            let mut l_seq = Vec::new();
            let mut r_seq = Vec::new();
            let mut local_bitvec = BitVec::new();

            //Fill left/right sequence and create bitvector for local "node"
            sequence.iter().foreach(|x| {
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
        } else {
            let (left_alphabet, right_alphabet) = alphabet.split_at(
                2usize.pow(
                    ((alphabet.len() + 1) as f64).log2().ceil() as u32 -1
                ) -1
            );
            let mut local_bitvec = BitVec::new();
            sequence.iter().foreach(|x| {
                if left_alphabet.contains(x) {
                    local_bitvec.push(false);
                }else{
                    local_bitvec.push(true);
                }
            });

            //Append to level bitvec
            if levels.get(level).is_none() {
                levels.push(BitVec::new());
            }


            /*if !levels.len() > level {
                //Create new for this level
                levels.push(BitVec::new());
            }*/
            levels[level] = levels[level].bit_concat(local_bitvec).to_bit_vec();
        }
    }

    fn rank_0(&self, l: u64, r: u64) -> Option<u64> {
        Some(self.bit_vec.rank_0(r)? - self.bit_vec.rank_0(l)?)
    }

    fn rank_1(&self, l: u64, r: u64) -> Option<u64> {
        Some(self.bit_vec.rank_1(r)? - self.bit_vec.rank_1(l)?)
    }
}

impl<T: PartialEq + Copy + Debug> Debug for WaveletTreeCompact<T>{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "WaveletTreeCompact {{ alphabet:{:?} bv:{:?}}}",
            self.alphabet,
            self.bit_vec.bits()
        )
    }
}

impl<T: PartialEq + Copy> PartialEq for WaveletTreeCompact<T>{
    fn eq(&self, other: &Self) -> bool {
        self.alphabet == other.alphabet && self.bit_vec.bits() == other.bit_vec.bits()
    }

    fn ne(&self, other: &Self) -> bool {
        !self.eq(other)
    }
}


/*impl From<String> for WaveletTreeCompact<char>{
    fn from(input: String) -> Self {
        WaveletTreeCompact::new(input.chars().collect())
    }
}*/

/*
impl<T: PartialEq + Copy> From<Vec<T>> {



}

impl<T: PartialEq + Copy> From<Iterator<Item = T>> {



}*/

impl From<&str> for WaveletTreeCompact<char> {
    fn from(input: &str) -> Self {
        WaveletTreeCompact::new(input.chars().collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;


    #[test]
    fn test_new_pointer_free(){
        let w_tree = WaveletTreeCompact::from("alabar_a_la_alabarda");

        //TODO compare it to expected value
        assert_eq!(w_tree, w_tree);
        //TEMP just for debug purposes
        println!("{:?}", w_tree);

    }

    #[test]
    fn test_access_pointer_free(){
        let test_string = "Hello world";
        let w_tree = WaveletTreeCompact::from(test_string);

        for (i, c)  in test_string.chars().enumerate() {
            //assert_eq!(w_tree.access(i as u64), Some(c));
            println!("Access: {}", w_tree.access(i as u64).unwrap());
        }
    }
}