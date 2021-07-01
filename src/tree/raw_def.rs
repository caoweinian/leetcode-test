//! Original definition of binary tree in leetcode, on which all the algorithms
//! and operations are performed.

use std::cell::RefCell;
use std::rc::Rc;

/// Leetcode definition of binary tree structure.
#[derive(Debug, PartialEq, Eq)]
pub struct TreeNode {
    pub val: i32,
    pub left: Option<Rc<RefCell<TreeNode>>>,
    pub right: Option<Rc<RefCell<TreeNode>>>,
}

impl TreeNode {
    /// Create a new node with value `val` and left & right child [`None`].
    #[inline]
    pub fn new(val: i32) -> Self {
        TreeNode {
            val,
            left: None,
            right: None,
        }
    }
}
