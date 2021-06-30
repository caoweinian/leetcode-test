//! The string presentations of definitions on leetcode. These variables will be helpful for preparing
//! leetcode workspace environment.

/// the definition of [`crate::tree::raw_def::TreeNode`] structure and the associated method
/// [`crate::tree::raw_def::TreeNode::new`].
pub const TREE_INIT_TEXT: &str = r"// Definition for a binary tree node.
// #[derive(Debug, PartialEq, Eq)]
// pub struct TreeNode {
//   pub val: i32,
//   pub left: Option<Rc<RefCell<TreeNode>>>,
//   pub right: Option<Rc<RefCell<TreeNode>>>,
// }
//
// impl TreeNode {
//   #[inline]
//   pub fn new(val: i32) -> Self {
//     TreeNode {
//       val,
//       left: None,
//       right: None
//     }
//   }
// }
use std::rc::Rc;
use std::cell::RefCell;";

/// Easy-to-input typedef of some tedious, but also useful structures
pub const TREE_SHORTCUTS_TEXT: &str = r"type TreeHandle = Option<Rc<RefCell<TreeNode>>>;
type ORRT = Option<Rc<RefCell<TreeNode>>>;
type RRT = Rc<RefCell<TreeNode>>;
type RT = RefCell<TreeNode>;";
