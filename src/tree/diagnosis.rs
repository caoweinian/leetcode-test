//! Most utilities for operating on [`TreeNode`].

use std::cell::RefCell;
use std::cmp::{max, Ordering};
use std::collections::VecDeque;
use std::fmt::{Display, Formatter, Write};
use std::rc::Rc;

use super::raw_def::TreeNode;
use super::shortcuts::{new_cell, new_node, new_rc, to_ptr, val as pointed};

pub type TreeHandle = Option<Rc<RefCell<TreeNode>>>;

/// The classic traversal types of binary tree.
#[derive(Ord, PartialOrd, Eq, PartialEq, Debug, Clone)]
pub enum TraversalType {
    /// pre-order
    PreOrder,
    /// in-order
    InOrder,
    /// post-order
    PostOrder,
    /// level order
    LevelOrder,
    // Rev...
}

#[derive(Debug, Eq, PartialEq)]
/// Error when constructing a binary tree.
pub enum TreeError {
    /// The tree structure cannot be determined by given two order.
    /// Theoretically, if every value occurs no more than once, a binary tree can be determined
    /// iif its in-order and another(pre-order, post-order or level-order) sequence are provided.
    ///
    /// Note that in some special cases a tree can also be determined(eg., pre-order and post-order
    /// both are "\[1\]"), but these cases are not handled and the corresponding `Nondeterministic`
    /// error will be returned.
    Nondeterministic(TraversalType, TraversalType),
    /// Parsing leetcode-format tree failed. It is either because you miss the square bracket, or
    /// if there is an element split by "," that cannot be parsed to [`i32`].
    LeetcodeFormatError,
}

impl Display for TreeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Nondeterministic(t1, t2) => f.write_fmt(format_args!(
                "tree structure cannot be determined by `{:?}` and `{:?}`",
                t1, t2
            )),
            Self::LeetcodeFormatError => f.write_str("leetcode format error"),
        }
    }
}

/// Associated function set for creating a binary tree.
pub struct TreeBuilder;

impl TreeBuilder {
    /// Build a binary tree using the parsed format in leetcode.
    ///
    /// Returns the root of the binary tree specified in `values`.
    ///
    /// # Safety
    ///
    /// You must make sure the `values` does be the valid input sequence of a binary tree, or the
    /// behaviour is undefined.
    ///
    /// # Examples
    ///
    /// ```
    /// use leetcode_test_utils::tree::TreeBuilder;
    /// use leetcode_test_utils::btree;
    ///
    /// let t1 = TreeBuilder::from_leetcode(&[]);
    /// assert_eq!(t1, btree!());
    ///
    /// let t2 = TreeBuilder::from_leetcode(&[Some(1), None, Some(2)]);
    /// assert_eq!(t2, btree!(1, null, 2));
    /// ```
    pub fn from_leetcode(values: &[Option<i32>]) -> TreeHandle {
        if values.is_empty() {
            return None;
        }
        let root = new_node(unsafe { (*values.get_unchecked(0)).unwrap() });
        let mut q: VecDeque<Rc<RefCell<TreeNode>>> = VecDeque::with_capacity(4); // avoid early frequent allocations
        q.push_back(Rc::clone(root.as_ref().unwrap())); // the `root` is always a `Rc`.

        for arr in values[1..].chunks(2) {
            let cur_head = q.pop_front().unwrap();
            unsafe {
                // safety: chunks(2) will always yield slice with len in {1, 2}.
                if let Some(left_child_val) = *arr.get_unchecked(0) {
                    let core = new_rc(left_child_val);
                    q.push_back(Rc::clone(&core));
                    // safety: always valid pointer
                    (*cur_head.as_ptr()).left = Some(core);
                }
                if arr.len() == 2 {
                    if let Some(right_child_val) = *arr.get_unchecked(1) {
                        let core = new_rc(right_child_val);
                        q.push_back(Rc::clone(&core));
                        // safety: always valid pointer
                        (*cur_head.as_ptr()).right = Some(core);
                    }
                }
            }
        }
        root
    }

    /// Build a binary tree using the raw format in leetcode(see [Leetcode binary tree representation](https://support.leetcode.com/hc/en-us/articles/360011883654-What-does-1-null-2-3-mean-in-binary-tree-representation-)).
    ///
    /// Returns the root of the binary tree specified in `s`, or [`Err`] indicating the parsing
    /// error.
    ///
    /// # Safety
    ///
    /// You must make sure that the parsed pure sequence does be the valid binary tree, or the
    /// behaviour is undefined.
    ///
    /// # Examples
    ///
    /// ```
    /// use leetcode_test_utils::tree::TreeBuilder;
    /// use leetcode_test_utils::btree;
    /// use leetcode_test_utils::tree::diagnosis::TreeError;
    ///
    /// let t1 = TreeBuilder::from_leetcode_raw("[]");
    /// assert_eq!(t1, Ok(btree!()));
    ///
    /// let t2 = TreeBuilder::from_leetcode_raw("[1,null,2]");
    /// assert_eq!(t2, Ok(btree!(1, null, 2)));
    ///
    /// let t3 = TreeBuilder::from_leetcode_raw("(1,null,2)");
    /// assert_eq!(t3.unwrap_err(), TreeError::LeetcodeFormatError);
    ///
    /// let t4 = TreeBuilder::from_leetcode_raw("[1,none,2]");
    /// assert_eq!(t4.unwrap_err(), TreeError::LeetcodeFormatError);
    ///
    /// let t5 = TreeBuilder::from_leetcode_raw("[1,12345678901,3]"); // '12345678901' overflows i32
    /// assert_eq!(t5.unwrap_err(), TreeError::LeetcodeFormatError);
    /// ```
    pub fn from_leetcode_raw(s: &str) -> Result<TreeHandle, TreeError> {
        if let [left_bracket, nums @ .., right_bracket] = s.as_bytes() {
            if *left_bracket != b'[' || *right_bracket != b']' {
                return Err(TreeError::LeetcodeFormatError);
            }
            if nums.is_empty() {
                return Ok(None);
            }
            let mut v = Vec::with_capacity(4);
            for n in unsafe { std::str::from_utf8_unchecked(nums) }.split(',') {
                if n == "null" {
                    v.push(None);
                } else {
                    match n.parse::<i32>() {
                        Ok(i) => v.push(Some(i)),
                        Err(_) => return Err(TreeError::LeetcodeFormatError),
                    }
                }
            }
            v.shrink_to_fit();
            Ok(Self::from_leetcode(&v))
        } else {
            Err(TreeError::LeetcodeFormatError)
        }
    }

    /// Build a binary tree with two specified orders and their sequences respectively.
    ///
    /// A binary tree(no value occurs more than once) can be built with in-order and another order
    /// (say, pre-order, post-order or level order). This function builds the corresponding tree.
    /// If the two types are not legal, or any invariance is compromised, returns an `Err`.
    ///
    /// This function is used when `seq1_type` or/and `seq2_type` is determined at runtime. If the types
    /// can be determined at compile time, use [`Self::from_pre_in`], [`Self::from_post_in`] or
    /// [`Self::from_level_in`] instead.
    ///
    /// # Arguments
    ///
    /// - `seq1_type` is the sequence type of `seq1`.
    /// - `seq2_type` is the sequence type of `seq2`.
    ///
    /// # Examples
    ///
    /// ```
    /// use leetcode_test_utils::tree::diagnosis::TraversalType;
    /// use leetcode_test_utils::tree::{TreeBuilder, T};
    /// use leetcode_test_utils::btree;
    ///
    /// let arg = 1;
    /// let type1 = match arg{   // determined at runtime
    ///     1 => TraversalType::PreOrder,
    ///     2 => TraversalType::PostOrder,
    ///     _ => TraversalType::LevelOrder,
    /// };
    /// let type2 = TraversalType::InOrder;
    ///
    /// let seq1 = vec![1, 4, 2, 8, 5, 7];  // also at runtime
    /// let seq2 = vec![4, 2, 1, 5, 7, 8];
    ///
    /// let tree = TreeBuilder::from_twos(type1, &seq1, type2, &seq2).unwrap();
    /// let target = btree!(1, 4, 8, null, 2, 5, null, null, null, null, 7);
    /// assert_eq!(tree, btree!(1, 4, 8, null, 2, 5, null, null, null, null, 7));
    /// ```
    pub fn from_twos(
        seq1_type: TraversalType,
        seq1: &[i32],
        seq2_type: TraversalType,
        seq2: &[i32],
    ) -> Result<TreeHandle, TreeError> {
        use TraversalType::*;
        match (seq1_type, seq2_type) {
            (PreOrder, InOrder) => Ok(Self::from_pre_in(seq1, seq2)),
            (InOrder, PreOrder) => Ok(Self::from_pre_in(seq2, seq1)),
            (PostOrder, InOrder) => Ok(Self::from_post_in(seq1, seq2)),
            (InOrder, PostOrder) => Ok(Self::from_post_in(seq2, seq1)),
            (LevelOrder, InOrder) => Ok(Self::from_level_in(seq1, seq2)),
            (InOrder, LevelOrder) => Ok(Self::from_level_in(seq2, seq1)),
            (o1, o2) => Err(TreeError::Nondeterministic(o1, o2)),
        }
    }

    /// Build a tree using pre-order and in-order structures.
    ///
    /// Returns the corresponding binary tree, or panics if some invariance is violated(a value occurs
    /// more than once, or pre_order.len() != in_order.len()).
    ///
    /// # Examples
    /// ```
    /// use leetcode_test_utils::btree;
    /// use leetcode_test_utils::tree::TreeBuilder;
    ///
    /// let tree = TreeBuilder::from_pre_in(&[2, 1, 3], &[1, 2, 3]);
    /// assert_eq!(tree, btree!(2, 1, 3));
    /// ```
    #[inline]
    pub fn from_pre_in(pre_order: &[i32], in_order: &[i32]) -> TreeHandle {
        assert_eq!(pre_order.len(), in_order.len(), "invariance violated");
        // fixme: replaced the recursion with iteration
        if pre_order.is_empty() {
            return None;
        }
        let value = unsafe { *pre_order.get_unchecked(0) };
        let pos = in_order
            .iter()
            .position(|&v| v == value)
            .expect("invariance violated");
        let ret = new_rc(unsafe { *in_order.get_unchecked(pos) });
        // fixme: replaced with raw pointer op?
        ret.borrow_mut().left = Self::from_pre_in(&pre_order[1..=pos], &in_order[..pos]);
        ret.borrow_mut().right = Self::from_pre_in(&pre_order[pos + 1..], &in_order[pos + 1..]);
        Some(ret)
    }

    /// Build a tree using post-order and in-order structures.
    ///
    /// Returns the corresponding binary tree, or panics if some invariance is violated(a value occurs
    /// more than once, or post_order.len() != in_order.len()).
    ///
    /// # Examples
    /// ```
    /// use leetcode_test_utils::btree;
    /// use leetcode_test_utils::tree::TreeBuilder;
    ///
    /// let tree = TreeBuilder::from_post_in(&[1, 3, 2], &[1, 2, 3]);
    /// assert_eq!(tree, btree!(2, 1, 3));
    /// ```
    pub fn from_post_in(post_order: &[i32], in_order: &[i32]) -> TreeHandle {
        assert_eq!(post_order.len(), in_order.len(), "invariance violated");
        // fixme: replaced the recursion with iteration
        if let Some((&value, post_order)) = post_order.split_last() {
            let pos = in_order
                .iter()
                .position(|&v| v == value)
                .expect("invariance violated");
            let ret = new_rc(unsafe { *in_order.get_unchecked(pos) });
            // fixme: replaced with raw pointer op?
            ret.borrow_mut().left = Self::from_post_in(&post_order[..pos], &in_order[..pos]);
            ret.borrow_mut().right = Self::from_post_in(&post_order[pos..], &in_order[pos + 1..]);
            Some(ret)
        } else {
            None
        }
    }

    /// Build a tree using level order and in-order structures.
    ///
    /// Returns the corresponding binary tree, or panics if some invariance is violated(a value occurs
    /// more than once, or level_order.len() != in_order.len()).
    ///
    /// # Examples
    /// ```
    /// use leetcode_test_utils::btree;
    /// use leetcode_test_utils::tree::TreeBuilder;
    ///
    /// let tree = TreeBuilder::from_level_in(&[1, 4, 8, 2, 5, 7], &[4, 2, 1, 5, 7, 8]);
    /// assert_eq!(tree, btree!(1, 4, 8, null, 2, 5, null, null, null, null, 7));
    /// ```
    #[inline]
    pub fn from_level_in(level_order: &[i32], in_order: &[i32]) -> TreeHandle {
        assert_eq!(level_order.len(), in_order.len(), "invariance violated");
        pub fn from_level_in_inner(level_order: &[i32], in_order: &[i32]) -> TreeHandle {
            if in_order.is_empty() {
                return None;
            }
            let (level_index, pos, value) = 'outer: loop {
                for (level_index, &level_value) in level_order.iter().enumerate() {
                    for (in_index, &in_value) in in_order.iter().enumerate() {
                        if level_value == in_value {
                            break 'outer (level_index, in_index, level_value);
                        }
                    }
                }
                panic!("invariance violated!");
            };
            let cell = new_cell(value);
            // fixme: replaced with raw pointer op?
            cell.borrow_mut().left =
                from_level_in_inner(&level_order[level_index + 1..], &in_order[..pos]);
            cell.borrow_mut().right =
                from_level_in_inner(&level_order[level_index + 1..], &in_order[pos + 1..]);
            Some(Rc::new(cell))
        }
        from_level_in_inner(level_order, in_order)
    }
}

/// Zero cost wrapper for [`Option<Rc<RefCell<TreeNode>>>`], also for bypassing the orphan rule.
/// There are many useful methods for operating on the binary tree as well.
#[derive(Debug, Clone)]
pub struct T(pub TreeHandle);

impl T {
    /// Get the height for the binary tree.
    ///
    /// Returns the height of the binary tree. The empty tree has height 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use leetcode_test_utils::btree;
    /// use leetcode_test_utils::tree::T;
    ///
    /// let tree1 = btree!(1, 2, 3);
    /// assert_eq!(T(tree1).height(), 2);
    /// assert_eq!(T(None).height(), 0);
    /// ```
    #[inline]
    pub fn height(&self) -> usize {
        unsafe { Self::height_maybe_null(to_ptr(self.0.as_ref())) }
    }

    /// Returns the height of the binary tree with given pointer as its root.
    #[inline]
    unsafe fn height_maybe_null(root: *const TreeNode) -> usize {
        if root.is_null() {
            0
        } else {
            Self::height_nonnull(root)
        }
    }

    /// Returns the height of the binary tree with given non-null pointer as its root.
    unsafe fn height_nonnull(root: *const TreeNode) -> usize {
        let mut stk = Vec::with_capacity(4);
        stk.set_len(1);
        *stk.get_unchecked_mut(0) = (root, 1);
        let mut max_height = 1_usize;
        while !stk.is_empty() {
            let (cur_node, h) = stk.pop().unwrap();
            max_height = max(max_height, h);
            if let Some(rc) = &(*cur_node).right {
                stk.push((rc.as_ptr(), h + 1));
            }
            if let Some(rc) = &(*cur_node).left {
                stk.push((rc.as_ptr(), h + 1));
            }
        }
        max_height
    }

    /// Returns the pre-order of the binary tree.
    pub fn pre_order(&self) -> Vec<i32> {
        if let Some(ref rc) = self.0 {
            let mut v = Vec::with_capacity(4);
            let mut ret = Vec::with_capacity(4);
            unsafe {
                v.set_len(1);
                *v.get_unchecked_mut(0) = rc.as_ptr() as *const TreeNode;
            }
            while !v.is_empty() {
                let top = v.pop().unwrap();
                ret.push(pointed(top));
                if let Some(rc) = unsafe { &(*top).right } {
                    v.push(rc.as_ptr());
                }
                if let Some(rc) = unsafe { &(*top).left } {
                    v.push(rc.as_ptr());
                }
            }
            ret.shrink_to_fit();
            ret
        } else {
            Default::default()
        }
    }

    /// Returns the in-order of the binary tree.
    #[inline]
    pub fn in_order(&self) -> Vec<i32> {
        // fixme: remove the recursion
        fn in_order_inner(root: *const TreeNode, v: &mut Vec<i32>) {
            if let Some(rc) = unsafe { &(*root).left } {
                in_order_inner(rc.as_ptr(), v);
            }
            v.push(pointed(root));
            if let Some(rc) = unsafe { &(*root).right } {
                in_order_inner(rc.as_ptr(), v);
            }
        }
        if let Some(ref rc) = self.0 {
            let mut v = Vec::with_capacity(4);
            in_order_inner(rc.as_ptr(), &mut v);
            v.shrink_to_fit();
            v
        } else {
            Default::default()
        }
    }

    /// Returns the post-order of the binary tree.
    pub fn post_order(&self) -> Vec<i32> {
        // fixme: remove the recursion
        fn post_order_inner(root: *const TreeNode, v: &mut Vec<i32>) {
            if let Some(rc) = unsafe { &(*root).left } {
                post_order_inner(rc.as_ptr(), v);
            }
            if let Some(rc) = unsafe { &(*root).right } {
                post_order_inner(rc.as_ptr(), v);
            }
            v.push(pointed(root));
        }
        if let Some(ref rc) = self.0 {
            let mut v = Vec::with_capacity(4);
            post_order_inner(rc.as_ptr(), &mut v);
            v.shrink_to_fit();
            v
        } else {
            Default::default()
        }
    }

    /// Returns the level order of the binary tree.
    pub fn level_order(&self) -> Vec<i32> {
        if let Some(ref rc) = self.0 {
            let mut q = VecDeque::with_capacity(4);
            q.push_back(rc.as_ptr() as *const TreeNode);
            let mut v = Vec::with_capacity(4);
            while !q.is_empty() {
                let top = q.pop_front().unwrap();
                v.push(pointed(top));
                if let Some(rc) = unsafe { &(*top).left } {
                    q.push_back(rc.as_ptr());
                }
                if let Some(rc) = unsafe { &(*top).right } {
                    q.push_back(rc.as_ptr());
                }
            }
            v.shrink_to_fit();
            v
        } else {
            Default::default()
        }
    }
    /// Launder the binary tree.
    ///
    /// Replace the current binary tree with a new representation, in which the structure and values is
    /// preserved respectively, but every reachable [`Rc`] will only have 1 strong count.
    ///
    /// This is helpful if you do not want the value in your tree changed through
    /// [`Rc<RefCell<TreeNode>>`] elsewhere.
    ///
    /// # Examples
    ///
    /// ```
    /// use leetcode_test_utils::btree;
    /// use leetcode_test_utils::tree::T;
    /// use std::rc::Rc;
    ///
    /// let tree = T(btree!(3));
    /// let evil = Rc::clone(tree.0.as_ref().unwrap());
    /// // the action below changes the value handled in `tree`, which may be unexpected
    /// evil.borrow_mut().val = 42;
    /// assert_ne!(tree.0.unwrap().borrow().val, 3);
    /// ```
    #[inline]
    pub fn re_owned(&mut self) {
        self.0 = self.detach().0;
    }

    /// Get the mirror tree.
    ///
    /// Returns a binary tree sharing the same structure and values handled by `self` except that
    /// every reachable [`Rc`] will only have 1 strong count.
    ///
    /// This is helpful if you want to get the tree structure without worrying about the values be soon
    /// changed by code elsewhere.
    ///
    /// # Examples
    ///
    /// ```
    /// use leetcode_test_utils::btree;
    /// use leetcode_test_utils::tree::T;
    /// use std::rc::Rc;
    ///
    /// let tree = T(btree!(3));
    /// let cannot_invade = tree.detach();
    /// cannot_invade.0.as_ref().unwrap().borrow_mut().val = 42;
    /// assert_eq!(tree.0.unwrap().borrow().val, 3);
    /// ```
    pub fn detach(&self) -> Self {
        // fixme: needs more efficient algorithm
        let v1 = self.pre_order();
        let v2 = self.in_order();
        Self(TreeBuilder::from_pre_in(&v1, &v2))
    }

    /// Test if the binary tree is balanced.
    ///
    /// # Example
    ///
    /// ```
    /// use leetcode_test_utils::btree;
    /// use leetcode_test_utils::tree::T;
    ///
    /// let tree1 = T(btree!(4, 2));
    /// assert!(tree1.is_balanced());
    ///
    /// let tree2 = T(btree!(4, 2, null, 1));
    /// assert!(!tree2.is_balanced())
    /// ```
    #[inline]
    pub fn is_balanced(&self) -> bool {
        fn is_balanced_inner(root: *const TreeNode) -> bool {
            if !root.is_null() {
                let left_ptr = to_ptr(unsafe { (*root).left.as_ref() });
                let right_ptr = to_ptr(unsafe { (*root).right.as_ref() });
                let mut h1 = unsafe { T::height_maybe_null(left_ptr) };
                let mut h2 = unsafe { T::height_maybe_null(right_ptr) };
                if h1 < h2 {
                    std::mem::swap(&mut h1, &mut h2);
                }
                h1 - h2 <= 1 && is_balanced_inner(left_ptr) && is_balanced_inner(right_ptr)
            } else {
                true
            }
        }
        is_balanced_inner(to_ptr(self.0.as_ref()))
    }

    /// Test if the binary tree is a BST(binary search tree).
    ///
    /// # Examples
    ///
    /// ```
    /// use leetcode_test_utils::btree;
    /// use leetcode_test_utils::tree::T;
    ///
    /// let tree = T(btree!(5, 2, 9, 1));
    /// assert!(tree.is_binary_search_tree());
    /// ```
    #[inline]
    pub fn is_binary_search_tree(&self) -> bool {
        // fixme: potential inefficient
        self.in_order()
            .windows(2)
            .all(|tp| unsafe { tp.get_unchecked(0).cmp(tp.get_unchecked(1)) } == Ordering::Less)
    }

    /// Returns the leetcode representation of the handled binary tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use leetcode_test_utils::tree::T;
    /// use leetcode_test_utils::btree;
    ///
    /// let tree = T(btree!(2, 4, null, 9));
    /// assert_eq!(tree.to_leetcode_raw(), "[2,4,null,9]");
    /// ```
    pub fn to_leetcode_raw(&self) -> String {
        let mut s = String::with_capacity(2);
        unsafe {
            let m = s.as_mut_vec();
            m.set_len(1);
            *m.get_unchecked_mut(0) = b'[';
        }
        debug_assert_eq!(s, "[");
        for o in self.to_leetcode() {
            if let Some(i) = o {
                s.write_fmt(format_args!("{},", i))
                    .expect("String::write_fmt() failed");
            } else {
                s.write_str("null,").expect("String::write_fmt() failed");
            }
        }
        let pos = s.as_bytes().len() - 1;
        unsafe {
            *s.as_mut_vec().get_unchecked_mut(pos) = b']';
        }
        s.shrink_to_fit();
        s
    }

    /// Returns the parsed leetcode representation of the handled binary tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use leetcode_test_utils::tree::T;
    /// use leetcode_test_utils::btree;
    ///
    /// let tree = T(btree!(2, 4, null, 9));
    /// assert_eq!(tree.to_leetcode(), vec![Some(2), Some(4), None, Some(9)]);
    /// ```
    pub fn to_leetcode(&self) -> Vec<Option<i32>> {
        if let Some(ref rc) = self.0 {
            let root = rc.as_ptr() as *const TreeNode;
            let mut ans = Vec::with_capacity(4);
            let mut q = VecDeque::with_capacity(4);
            q.push_back(root);
            while !q.is_empty() {
                let top = q.pop_front().unwrap();
                if top.is_null() {
                    ans.push(None);
                } else {
                    ans.push(Some(pointed(top)));
                    q.push_back(to_ptr(unsafe { (*top).left.as_ref() }));
                    q.push_back(to_ptr(unsafe { (*top).right.as_ref() }));
                }
            }
            ans.truncate(ans.iter().rev().skip_while(|o| o.is_none()).count());
            ans
        } else {
            Default::default()
        }
    }

    /// Returns the len of the binary tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use leetcode_test_utils::tree::T;
    /// use leetcode_test_utils::btree;
    ///
    /// let tree = T(btree!(2, 4, null, 9));
    /// assert_eq!(tree.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        if let Some(ref rc) = self.0 {
            let mut v = Vec::with_capacity(4);
            let mut ret = 0_usize;
            unsafe {
                v.set_len(1);
                *v.get_unchecked_mut(0) = rc.as_ptr() as *const TreeNode;
            }
            while !v.is_empty() {
                let top = v.pop().unwrap();
                ret += 1;
                if let Some(rc) = unsafe { &(*top).right } {
                    v.push(rc.as_ptr());
                }
                if let Some(rc) = unsafe { &(*top).left } {
                    v.push(rc.as_ptr());
                }
            }
            ret
        } else {
            0
        }
    }
}

// 2021/7/1; In progress
// #[derive(Debug)]
// pub struct ForestCmpResult {
//     requires_answer: Vec<String>,
//     not_answer: Vec<String>,
//     accepted: Vec<String>,
// }
//
//
// pub fn forest_eq_seq_insensitive(output: &[TreeHandle], answer: &str) -> ForestCmpResult {
//     unimplemented!()
// }

impl Display for T {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.to_leetcode_raw())
    }
}

impl PartialEq for T {
    fn eq(&self, other: &Self) -> bool {
        // fixme: needs more efficient algorithm
        self.pre_order().eq(&other.pre_order()) && self.in_order().eq(&other.in_order())
    }
}

/// Construct a binary tree using the leetcode sequence format, excluding the square brackets.
#[macro_export]
macro_rules! btree {
    () => { None };
    ($($val: expr),+ $(,)?) => {
        {
            let values = vec![$(stringify!($val)),+].iter()
                        .map(|v|v.parse::<i32>().ok())
                        .collect::<Vec<Option<i32>>>();
            leetcode_test_utils::tree::TreeBuilder::from_leetcode(values.as_slice())
        }
    };
}

/// Rapidly create a left child of the given node.
///
/// # Examples
///
/// ```
/// use leetcode_test_utils::{new_left, btree};
/// use leetcode_test_utils::tree::shortcuts::new_node;
/// use leetcode_test_utils::tree::T;
///
/// let root = new_node(42);
/// new_left!(root.as_ref().unwrap(), 10);
/// assert_eq!(T(root), T(btree!(42, 10)));
/// ```
#[macro_export]
macro_rules! new_left {
    ($rc: expr, $val: expr) => {
        $rc.borrow_mut().left = leetcode_test_utils::tree::shortcuts::new_node($val);
    };
}

/// Rapidly create a right child of the given node.
///
/// # Examples
///
/// ```
/// use leetcode_test_utils::{new_right, btree};
/// use leetcode_test_utils::tree::shortcuts::new_node;
/// use leetcode_test_utils::tree::T;
///
/// let root = new_node(42);
/// new_right!(root.as_ref().unwrap(), 10);
/// assert_eq!(T(root), T(btree!(42, null, 10)));
/// ```
#[macro_export]
macro_rules! new_right {
    ($rc: expr, $val: expr) => {
        $rc.borrow_mut().right = leetcode_test_utils::tree::shortcuts::new_node($val);
    };
}

/// Rapidly create left & right children of the given node.
///
/// # Examples
///
/// ```
/// use leetcode_test_utils::{new_child, btree};
/// use leetcode_test_utils::tree::shortcuts::new_node;
/// use leetcode_test_utils::tree::T;
///
/// let root = new_node(42);
///
/// new_child!(root.as_ref().unwrap(), left, 2);
/// assert_eq!(T(root.clone()), T(btree!(42, 2)));
///
/// new_child!(root.as_ref().unwrap(), l, 3);
/// assert_eq!(T(root.clone()), T(btree!(42, 3)));
///
/// new_child!(root.as_ref().unwrap(), L, 4);
/// assert_eq!(T(root.clone()), T(btree!(42, 4)));
///
/// new_child!(root.as_ref().unwrap(), right, 5);
/// assert_eq!(T(root.clone()), T(btree!(42, 4, 5)));
///
/// new_child!(root.as_ref().unwrap(), r, 6);
/// assert_eq!(T(root.clone()), T(btree!(42, 4, 6)));
///
/// new_child!(root.as_ref().unwrap(), R, 7);
/// assert_eq!(T(root.clone()), T(btree!(42, 4, 7)));
///
/// new_child!(root.as_ref().unwrap(), [8, 9]);
/// assert_eq!(T(root.clone()), T(btree!(42, 8, 9)));
/// ```
#[macro_export]
macro_rules! new_child {
    ($rc:expr, left, $val:expr) => {
        leetcode_test_utils::new_left!($rc, $val);
    };
    ($rc:expr, l, $val:expr) => {
        leetcode_test_utils::new_left!($rc, $val);
    };
    ($rc:expr, L, $val:expr) => {
        leetcode_test_utils::new_left!($rc, $val);
    };
    ($rc:expr, right, $val:expr) => {
        leetcode_test_utils::new_right!($rc, $val);
    };
    ($rc:expr, r, $val:expr) => {
        leetcode_test_utils::new_right!($rc, $val);
    };
    ($rc:expr, R, $val:expr) => {
        leetcode_test_utils::new_right!($rc, $val);
    };
    ($rc:expr, [$left:expr, $right:expr]) => {
        leetcode_test_utils::new_left!($rc, $left);
        leetcode_test_utils::new_right!($rc, $right);
    };
}
