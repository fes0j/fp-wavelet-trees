use bio::data_structures::rank_select::RankSelect;
use bv::BitVec;
use bv::BitsMut;
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
}

/*impl<T: PartialEq + Copy> WaveletTree<T> for WaveletTreeCompact<T> {

}*/

impl<T: PartialEq + Copy> WaveletTreeCompact<T> {
    pub fn new(input: Vec<T>) -> WaveletTreeCompact<T> {
        //Create alphabet
        let mut alphabet: Vec<T> = Vec::new();
        input.iter().map(|x| {
            if !alphabet.contains(&x) {
                alphabet.push(*x);
            }
        }).count();

        //Create vector for levels
        let mut levels: Vec<BitVec<u8>> = Vec::new();

        //Create bitvecs for levels
        WaveletTreeCompact::create_bitvec(0, &mut levels, &input[..], &alphabet[..]);

        //Append all the levels into one big bitvec
        let bit_vec:BitVec<u8> = BitVec::new();
        for l in levels {
            bit_vec.bit_concat(l);
        }

        WaveletTreeCompact {
            alphabet: alphabet.to_owned(),
            bit_vec: RankSelect::new(bit_vec, 1),
        }
    }

    fn create_bitvec(level: usize, levels: &mut Vec<BitVec<u8>>, sequence: &[T], alphabet: &[T]) {
        if alphabet.len() >= 2 {
            //Split alphabet
            let (left_alphabet, right_alphabet) = alphabet.split_at(
                2usize.pow(
                    ((alphabet.len() + 1) as f64).ln().ceil() as u32
                )
            );
            let mut l_seq = Vec::new();
            let mut r_seq = Vec::new();
            let mut local_bitvec = BitVec::new();

            //Fill left/right sequence and create bitvector for local "node"
            sequence.iter().map(|x| {
                if left_alphabet.contains(x) {
                    l_seq.push(*x);
                    local_bitvec.push(false);
                } else {
                    r_seq.push(*x);
                    local_bitvec.push(true);
                }
            }).count();


            //Append to level bitvec
            if !levels.len() > level {
                //Create new for this level
                levels.push(BitVec::new());
            }
            levels[level].bit_concat(local_bitvec);

            //Call recursively for childs
            WaveletTreeCompact::create_bitvec(level + 1, levels, &l_seq[..], left_alphabet); //Left needs to be first!!
            WaveletTreeCompact::create_bitvec(level + 1, levels, &r_seq[..], right_alphabet);
        } else {}
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


        assert_eq!(w_tree, w_tree);
        println!("{:?}", w_tree);

    }
}