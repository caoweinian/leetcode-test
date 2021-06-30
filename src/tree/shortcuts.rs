//! Wraps a value in [`TreeNode`] all in one function, of any scale.

use super::raw_def::TreeNode;
use std::cell::RefCell;
use std::ptr::{null, null_mut};
use std::rc::Rc;

/// Create a [`RefCell<TreeNode>`] with given value.
///
/// This function is trivial. It only lets you avoid writing bunches of boiler plate code "::new(...)".
///
/// # Examples
///
/// ```
/// use leetcode_test_utils::tree::shortcuts::new_cell;
/// let cell = new_cell(42);
/// assert_eq!(cell.borrow().val, 42);
/// ```
#[inline]
pub fn new_cell(val: i32) -> RefCell<TreeNode> {
    RefCell::new(TreeNode::new(val))
}

/// Create a [`Rc<RefCell<TreeNode>>`] with given value.
///
/// This function is trivial. It only lets you avoid writing bunches of boiler plate code "::new(...)".
///
/// # Examples
///
/// ```
/// use leetcode_test_utils::tree::shortcuts::new_rc;
/// let rc = new_rc(42);
/// assert_eq!(rc.borrow().val, 42);
/// ```
#[inline]
pub fn new_rc(val: i32) -> Rc<RefCell<TreeNode>> {
    Rc::new(RefCell::new(TreeNode::new(val)))
}

/// Create a complete node([`Option<Rc<RefCell<TreeNode>>>`]) with given value.
///
/// This function is trivial. It only lets you avoid writing bunches of boiler plate code "::new(...)".
///
/// # Examples
///
/// ```
/// use leetcode_test_utils::tree::shortcuts::new_node;
/// let node = new_node(42);
/// assert_eq!(node.unwrap().borrow().val, 42);
/// ```
#[inline]
pub fn new_node(val: i32) -> Option<Rc<RefCell<TreeNode>>> {
    Some(Rc::new(RefCell::new(TreeNode::new(val))))
}

/// Access the value pointed by the given pointer.
///
/// This function is a shortcut for getting the value pointed by `p`.
/// It is often used for pointer gotten by calling `as_ptr()` on whatever coerces to [`RefCell<TreeNode>`].
///
/// # Safety
///
/// - The pointer **must not** be null, or the program will crash.
///
/// # Examples
///
/// ```
/// use leetcode_test_utils::tree::shortcuts::{new_node, val};
/// let node = new_node(42);
/// let pointer = node.as_ref().unwrap().as_ptr();
/// assert_eq!(val(pointer), 42);
/// ```
#[inline]
pub fn val(p: *const TreeNode) -> i32 {
    unsafe { (*p).val }
}

/// Convert the rust style mutable pointer(specified in leetcode) into C/C++ style immutable pointer.
///
/// Returns the immutable pointer handled by `root` if it is [`Some`], or [`std::ptr::null()`] is returned.
/// Rust is so famous for its safety, in which the most safe way to operate on a pointer is to
/// borrow a [`RefCell`] at runtime. But sometimes you really want to let the program perform the
/// best(yeah, you do not want to be penalized anyway) as if you run the corresponding raw C/C++ code.
/// This function provides the highway for you. **Be careful**!
///
/// # Examples
///
/// ```
/// use leetcode_test_utils::tree::shortcuts::{new_node, to_ptr};
/// use leetcode_test_utils::btree;
/// let root = btree!(42, 10);  // ok, `root->left->val` is 10
/// unsafe{
///     assert_eq!((*to_ptr((*to_ptr(root.as_ref())).left.as_ref())).val, 10);
/// }
/// assert_eq!(to_ptr(None), std::ptr::null());
/// ```
#[inline]
pub fn to_ptr(root: Option<&Rc<RefCell<TreeNode>>>) -> *const TreeNode {
    root.map_or(null(), |r| r.as_ptr())
}

/// Convert the rust style mutable pointer(specified in leetcode) into C/C++ style mutable pointer.
///
/// Returns the mutable pointer handled by `root` if is [`Some`], or [`std::ptr::null_mut()`] is
/// returned. Rust is so famous for its safety, in which the most safe way to operate on a pointer
/// is to borrow a [`RefCell`] at runtime. But sometimes you really want to let the program perform
/// the best(yeah, you do not want to be penalized anyway) as if you run the corresponding raw C/C++
/// code. This function provides the railway for you. **Be CAREFUL**!
///
/// # Examples
///
/// ```
/// use leetcode_test_utils::tree::shortcuts::to_ptr_mut;
/// use leetcode_test_utils::tree::T;
/// use leetcode_test_utils::btree;
///
/// let root = btree!(42, null, 50);
/// let ptr_root_right = to_ptr_mut(root.as_ref());
/// unsafe{
///     (*ptr_root_right).val = 45;
/// }
/// let tree1 = T(root);
/// let tree2 = T(btree!(45, null, 50));
/// assert_eq!(tree1, tree2);
/// ```
#[inline]
pub fn to_ptr_mut(root: Option<&Rc<RefCell<TreeNode>>>) -> *mut TreeNode {
    root.map_or(null_mut(), |r| r.as_ptr())
}
