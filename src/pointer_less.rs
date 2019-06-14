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
    sequence_length: u64
}

/*impl<T: PartialEq + Copy> WaveletTree<T> for WaveletTreeCompact<T> {

}*/

impl<T: PartialEq + Copy> WaveletTreeCompact<T> {
    pub fn new(input: Vec<T>) -> WaveletTreeCompact<T> {
        let sequence_length = input.len() as u64;
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

        //Append all the levels into one big bitvec
        let bit_vec:BitVec<u8> = BitVec::new();
        for l in levels {
            bit_vec.bit_concat(l);
        }

        WaveletTreeCompact {
            alphabet: alphabet.to_owned(),
            bit_vec: RankSelect::new(bit_vec, 1),
            sequence_length
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
            sequence.iter().map(|x| {
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
            levels[level]=bit_concat(local_bitvec);

            //Call recursively for childs
            WaveletTreeCompact::create_bitvec(level + 1, levels, &l_seq[..], left_alphabet); //Left needs to be first!!
            WaveletTreeCompact::create_bitvec(level + 1, levels, &r_seq[..], right_alphabet);
        } else {}
    }
    
    fn splitalphabet<'a>(alphabet: &'a[T]) -> (&[T],&[T]){
        if alphabet.len()==0{
            panic!("can not split empty alphabet")
        }else{
            alphabet.split_at(
                    2usize.pow(
                        ((alphabet.len()+1) as f64).log2().ceil() as u32 -1
                    )-1
            )
        }
    }
    
    fn rank(&self, object: T, n: u64) -> Option<u64> {
        self.rank_intern(&self.alphabet[..],object,n,0,self.sequence_length-1)
    }
    
    fn rank_intern(&self,alphabet: &[T], object: T, n: u64, left: u64, right: u64) -> Option<u64> {
        //Split alphabet
        let (left_alphabet, right_alphabet) = WaveletTreeCompact::splitalphabet(alphabet);
        if left_alphabet.contains(&object) {
            if left_alphabet.len()==1 {
                match (self.bit_vec.rank_0(left+n),self.bit_vec.rank_0(left)){
                    (Some(i),Some(j)) => Some(i-j),
                    _ => None
                }
            }else{
                //assert!(self.bit_vec.rank_0(left).is_some());
                if let (Some(l),Some(r)) = (self.bit_vec.rank_0(left),self.bit_vec.rank_0(right)){
                //in case there is a child
                let left_child_left = left+self.sequence_length;
                let left_child_right = left_child_left+r-l-1;
                let right_child_left = left_child_right+1;
                let right_child_right = right+self.sequence_length;
                assert!(right_child_right-left_child_left==right-left);
                self.rank_intern(left_alphabet,object, n,left_child_left,left_child_right)
                }else{
                    //out of bounds
                    panic!("rank: no child in tree");
                }
            }
        } else if right_alphabet.contains(&object) {
            if right_alphabet.len()==1 {
                match (self.bit_vec.rank_1(right+n),self.bit_vec.rank_1(right)){
                    (Some(i),Some(j)) => Some(i-j),
                    _ => None
                }
            }else{
                if let (Some(l),Some(r)) = (self.bit_vec.rank_0(left),self.bit_vec.rank_0(right)){
                //in case there is a child
                let left_child_left = left+self.sequence_length;
                let left_child_right = left_child_left+r-l-1;
                let right_child_left = left_child_right+1;
                let right_child_right = right+self.sequence_length;
                assert!(right_child_right-left_child_left==right-left);
                self.rank_intern(right_alphabet,object, n,right_child_left,right_child_right)
                }else{
                    //out of bounds
                    panic!("rank: no child in tree");
                }
            }
        }else{None}
        
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

#[cfg(test)]
mod tests {
    use super::*;
    use unicode_segmentation::UnicodeSegmentation;

    #[test]
    fn test_new(){
        let w_tree = WaveletTreeCompact::new("alabar_a_la_alabarda".chars().collect());

        println!("{:?}", w_tree);

    }
    
    #[test]
    fn test_rank_5_letter() {
        let test_string = "abcde".chars().collect();
        let mut w_tree = WaveletTreeCompact::new(test_string);

        assert!(w_tree.bit_vec.bits().len()>0);
        
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
}
