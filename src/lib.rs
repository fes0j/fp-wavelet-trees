use bio::data_structures::rank_select::RankSelect;
use bv::BitVec;
use bv::BitsMut;


pub struct WavletTree {
    //binaryTree
    //alpahbet
}

impl WavletTree {
    pub fn new(placeholder: &str){
        //new tree from parameter
    }
    pub fn deserialize(placeholder: &str){
        //deserialize
    }
    pub fn serialize(&self){
        //serialize
    }
    pub fn access(position: u32){
        //resolve character at position
    }
    pub fn select(character: char, n: u32){
        //return position of n-th character
    }
    pub fn rank(character: char, n: u32){
        //number of characters until position n
    }
}

struct WavletTreeNode {
    bit_vec: RankSelect,
    left_child: Box<Option<WavletTreeNode>>,
    right_child: Box<Option<WavletTreeNode>>,
}
impl WavletTreeNode {
    fn new(string: Vec<char>, alphabet: &Vec<char>) -> Option<WavletTreeNode>{
        if alphabet.len() > 2 {
            //split alphabet
            let string_length = string.len();
            let (l_a,r_a) = alphabet.split_at(alphabet.len()/2);
            let mut left_alphabet = l_a.to_vec();
            let mut right_alphabet = r_a.to_vec();
            //create bitmap of string lenth
            let mut bitvector : BitVec<u8>= BitVec::with_capacity(string_length as u64);
            let mut left_string : Vec<char>= Vec::new();
            let mut right_string : Vec<char>= Vec::new();
            for i in (0..string_length) {
                //assign bitmap 0/1s
                let c = string.get(i).unwrap();
                let bl = r_a.contains(c);
                bitvector.set_bit(i as u64, bl);
                //fill partial strings
                if bl{
                    right_string.push(*c);
                }else{
                    left_string.push(*c);
                }
            }
            //create rankselect structure
            let rs = RankSelect::new(bitvector, 1);
            Some(WavletTreeNode{
                bit_vec: rs,
                //recusivley create left/right child from substring and partial alphabet
                left_child: Box::new(WavletTreeNode::new(left_string,&left_alphabet)),
                right_child: Box::new(WavletTreeNode::new(right_string,&right_alphabet)),
            })
        }else{
            None
        }
    }
    fn select(position: u32, alphabet: Vec<char>) -> char{
        //switch on 0/1
        //newpos=rank 0/1
        //split alphabet
        //recursivley select(newpos,left/right-alphabet
        'a'
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    //TODO: write tests
}
