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
    pub fn serialize(){
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
    //bio bitmap
    left_child: Box<Option<WavletTreeNode>>,
    right_child: Box<Option<WavletTreeNode>>,
}
impl WavletTreeNode {
    fn select(position: u32, alphabet: Vec<char>){
        //switch on 0/1
        //newpos=rank 0/1
        //split alphabet
        //recursivley select(newpos,left/right-alphabet
    }
}
