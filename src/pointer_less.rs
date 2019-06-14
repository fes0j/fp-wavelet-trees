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
        unimplemented!()
    }

    fn select(&self, object: T, n: u64) -> Option<u64> {
        unimplemented!()
    }

    fn rank(&self, object: T, n: u64) -> Option<u64> {
        self.rank_intern(&self.alphabet[..],object,n,0,self.sequence_len-1)
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
        WaveletTreeCompact::create_bitvec(0, &mut levels, &input[..], &alphabet[..]);

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

            let (left_alphabet, right_alphabet) = WaveletTreeCompact::splitalphabet(alphabet);

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
            /*let (left_alphabet, right_alphabet) = alphabet.split_at(
                2usize.pow(
                    ((alphabet.len() + 1) as f64).log2().ceil() as u32 -1
                ) -1
            );
            let mut local_bitvec = Bitvec::new();
            sequence.iter().foreach(|x| {
                if left_alp
            });*/
        }
    }

    fn rank_0(&self, l: u64, r: u64) -> Option<u64> {
        Some(self.bit_vec.rank_0(r)? - self.bit_vec.rank_0(l)?)
    }

    fn rank_1(&self, l: u64, r: u64) -> Option<u64> {
        Some(self.bit_vec.rank_1(r)? - self.bit_vec.rank_1(l)?)
    }
    
    fn splitalphabet<'a>(alphabet: &'a[T]) -> (&[T],&[T]){
        if alphabet.len()==0{
            panic!("can not split empty alphabet")
        }else{
            alphabet.split_at(
                    2usize.pow(
                        ((alphabet.len()) as f64).log2().ceil() as u32 -1
                    )
            )
        }
    }
    
    fn rank_intern(&self,alphabet: &[T], object: T, n: u64, left: u64, right: u64) -> Option<u64> {
        //Split alphabet
        assert!(left != right);
        let (left_alphabet, right_alphabet) = WaveletTreeCompact::splitalphabet(alphabet);
        if left_alphabet.contains(&object) {
            if left_alphabet.len()==1 {
                //need to account for the left most bit itselfe but can not rely on left>0
                match (self.bit_vec.rank_0(left+n),self.bit_vec.rank_0(left)){
                    (Some(i),Some(j)) => match self.bit_vec.bits()[left] {
                                            true => Some(i-j),
                                            false => Some(i-j+1)}
                    _ => None
                }
            }else{
                //assert!(self.bit_vec.rank_0(left).is_some());
                if let (Some(l),Some(r)) = (self.bit_vec.rank_0(left),self.bit_vec.rank_0(right)){
                //in case there is a child
                let left_child_left = left+self.sequence_len;
                let left_child_right = left_child_left+r-l-1;
                let right_child_left = left_child_right+1;
                let right_child_right = right+self.sequence_len;
                self.rank_intern(left_alphabet,object, n,left_child_left,left_child_right)
                }else{
                    //out of bounds
                    panic!("rank: no child in tree");
                }
            }
        } else if right_alphabet.contains(&object) {
            if right_alphabet.len()==1 {
                //need to account for the left most bit itselfe but can not rely on left>0
                match (self.bit_vec.rank_1(right+n),self.bit_vec.rank_1(right)){
                    (Some(i),Some(j)) => match self.bit_vec.bits()[left] {
                                            true => Some(i-j+1),
                                            false => Some(i-j)}
                    _ => None
                }
            }else{
                if let (Some(l),Some(r)) = (self.bit_vec.rank_0(left),self.bit_vec.rank_0(right)){
                //in case there is a child
                let left_child_left = left+self.sequence_len;
                let left_child_right = left_child_left+r-l-1;
                let right_child_left = left_child_right+1;
                let right_child_right = right+self.sequence_len;
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
    fn test_new(){
        let w_tree = WaveletTreeCompact::new("alabar_a_la_alabarda".chars().collect());

        println!("{:?}", w_tree);

    }
    
    #[test]
    fn test_rank_2_letters(){
        let test_string = "aaaaabbbbbcde".chars().collect();
        let mut w_tree = WaveletTreeCompact::new(test_string);
        
        assert_eq!(w_tree.rank('a', 0), Some(1));
        assert_eq!(w_tree.rank('a', 1), Some(2));
        assert_eq!(w_tree.rank('a', 2), Some(3));
        assert_eq!(w_tree.rank('a', 3), Some(4));
        assert_eq!(w_tree.rank('a', 4), Some(5));
        assert_eq!(w_tree.rank('a', 5), Some(5));
        assert_eq!(w_tree.rank('a', 6), Some(5));
    }
    
    #[test]
    fn test_split_alphabet(){
        let alphabet :Vec<char>="abcde".chars().collect();
        let (l,r)=WaveletTreeCompact::splitalphabet(&alphabet[..]);
        
        assert!(alphabet.len()==5);
        assert_eq!(l.len(),4);
        assert_eq!(r.len(),1);
        
        let test_string = "abcde".chars().collect();
        let mut w_tree = WaveletTreeCompact::new(test_string);
        
        assert_eq!(w_tree.bit_vec.bits()[0],false);
        assert_eq!(w_tree.bit_vec.bits()[1],false);
        assert_eq!(w_tree.bit_vec.bits()[2],false);
        assert_eq!(w_tree.bit_vec.bits()[3],false);
        assert_eq!(w_tree.bit_vec.bits()[4],true);
        assert_eq!(w_tree.bit_vec.bits()[5],false);
    }
    
    #[test]
    fn test_rank_5_letter() {
        let test_string = "abcde".chars().collect();
        let mut w_tree = WaveletTreeCompact::new(test_string);
        
        assert_eq!(w_tree.rank('a', 3), Some(1));
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
