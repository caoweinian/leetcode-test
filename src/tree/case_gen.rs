//! 2021.6.30; This module is not finished yet.

use super::TreeHandle;

pub enum GenError {
    WillOverflow,
    IllegalRate,
}

pub type Bone = Vec<bool>;
pub type Result<T> = std::result::Result<T, GenError>;

pub struct BoneBuilder;

pub enum Direction {
    OneWayLeft,
    OneWayRight,
    Random,
}

impl BoneBuilder {
    pub fn fixed_len_one(tree_len: u32) -> Bone {
        unimplemented!()
    }

    pub fn fixed_len_drained(tree_len: u32) -> Result<Vec<Bone>> {
        unimplemented!()
    }

    pub fn fixed_len_drained_lte(tree_len_ub: u32) -> Result<Vec<Bone>> {
        unimplemented!()
    }

    pub fn fixed_len_rate(rate: f64) -> Result<Vec<Bone>> {
        unimplemented!()
    }

    pub fn fixed_len_nodup(tree_len: u32, tree_num: u32) -> Result<Vec<Bone>> {
        unimplemented!()
    }

    pub fn linked_list(tree_len: u32, d: Direction) -> Bone {
        unimplemented!()
    }

    pub fn linked_list_custom(tree_len: u32, random_len: u32) -> (Bone, Bone, Vec<Bone>) {
        unimplemented!()
    }

    pub fn heap(tree_len: u32) -> Bone {
        unimplemented!()
    }

    pub fn heap_lte(tree_len_ub: u32) -> Vec<Bone> {
        unimplemented!()
    }

    pub fn pyramid(height: u8) -> Result<Bone> {
        unimplemented!()
    }

    pub fn pyramid_lte(height_ub: u8) -> Result<Bone> {
        unimplemented!()
    }

    pub fn complete(nonleaf_len: u32) -> Result<Bone> {
        unimplemented!()
    }
}

#[derive(Eq, PartialEq, Debug, Copy, Clone)]
pub enum Distribution {
    Sorted,
    UniqueSorted,
    Uni(Option<i32>),
    Random,
}

#[derive(Eq, PartialEq, Debug, Copy, Clone)]
pub enum SeqRange {
    Positive,
    NonNegative,
    NonPositive,
    Negative,
    Z,
}

#[derive(Debug)]
struct ValueRenderer<'a> {
    data: &'a [Bone],
    pub dist: Distribution,
    pub r: SeqRange,
}

impl<'a> ValueRenderer<'a> {
    #[inline]
    pub fn new(data: &'a [Bone]) -> Self {
        Self {
            data,
            dist: Distribution::Random,
            r: SeqRange::Z,
        }
    }

    #[inline]
    pub fn from(data: &'a [Bone], dist: Distribution, r: SeqRange) -> Self {
        Self { data, dist, r }
    }

    #[inline]
    pub fn reset(&'a mut self, b: &'a [Bone]) {
        self.data = b;
    }

    pub fn get(&self) -> Vec<TreeHandle> {
        unimplemented!()
    }
}

// #[derive(Debug, Clone)]
// pub enum Subset {
//     Default,
//     // of len *
//     FixedLen(u32),
//     // of height *
//     FixedHeight(u32),
//     // of height no more than *
//     SingleList(u32),
//     // of height no more than *
//     FullShape(u8),
//     // of len no more than *
//     HeapShape(u32),
//     // of len no more than *
//     CompleteShape(u32),
//     // of shapes specified in *
//     Shape(Vec<Bone>),
// }
//
// #[derive(Debug, Copy, Clone)]
// pub enum StopWhen {
//     StructureDrained,
//     TriedTimes(u32),
//     TimesUp(Duration),
//     GotNums(u32),
//     GotRate(f64),
// }
//
// #[derive(Debug, Copy, Clone)]
// pub enum ValueDistribution {
//     Sorted,
//     UniqueSorted,
//     Unique(Option<i32>),
//     Random,
// }
//
// #[derive(Debug)]
// pub struct GenOptions {
//     subset: Subset,
//     stop_when: StopWhen,
//     distribution: ValueDistribution,
//     range: Option<HashSet<i32>>,
//     timeout: Option<Duration>,
// }
//
// #[derive(Debug, Eq, PartialEq)]

//
// impl GenOptions {
//     pub fn new() -> GenOptions {
//         Self {
//             subset: Subset::Default,
//             stop_when: StopWhen::GotNums(4096),
//             distribution: ValueDistribution::Random,
//             range: None,
//             timeout: None,
//         }
//     }
//
//     #[inline]
//     pub fn subset(mut self, s: Subset) -> Self {
//         self.subset = s;
//         self
//     }
//
//     #[inline]
//     pub fn stop_when(mut self, when: StopWhen) -> Self {
//         self.stop_when = when;
//         self
//     }
//
//     #[inline]
//     pub fn distribution(mut self, d: ValueDistribution) -> Self {
//         self.distribution = d;
//         self
//     }
//
//     #[inline]
//     pub fn range(mut self, r: HashSet<i32>) -> Self {
//         self.range = Some(r);
//         self
//     }
//
//     #[inline]
//     pub fn timeout(mut self, d: Duration) -> Self {
//         self.timeout = Some(d);
//         self
//     }
//
//     /* priv */ fn gen(self) -> Result<Vec<TreeHandle>, GenError> {
//         unimplemented!()
//     }
//
//     /* priv */ unsafe fn gen_everything_unchecked(self) -> Vec<TreeHandle> {
//         unimplemented!()
//     }
//
//     pub fn test(&self) -> Result<(), GenError> {
//         if let Subset::FixedHeight(u) = self.subset{
//             if n > 32{
//                 return Err(GenError::WillOverflowU32(self.subset.clone(), self.stop_when))
//             }
//         }
//
//         Ok(())
//     }
// }
//
// pub struct Engine(Vec<GenOptions>);
//
// impl Engine {
//     pub fn new() -> Self {
//         unimplemented!()
//     }
//
//     pub fn with_capacity(cap: usize) -> Self {
//         unimplemented!()
//     }
//
//     pub fn add(opt: GenOptions) {
//         unimplemented!()
//     }
//
//     pub fn run(self) -> Result<TreeSetFilter, GenError> {
//         let mut v = vec![2, 3, 4];
//         unimplemented!()
//     }
// }
//
// pub struct TreeSetFilter(Vec<TreeHandle>);
//
// impl TreeSetFilter {
//     #[inline]
//     pub fn sort_by_cached_key_and_then_dedup_by<K, KeyCluster, Dedup>
//     (&mut self, f: KeyCluster, mut d: Dedup)
//         where
//             K: Ord,
//             KeyCluster: FnMut(&TreeHandle) -> K,
//             Dedup: FnMut(&mut TreeHandle, &mut TreeHandle) -> bool {
//         self.0.sort_by_cached_key(f);
//         self.0.dedup_by(d);
//     }
//
//     #[inline]
//     pub fn get(self) -> Vec<TreeHandle> { self.0 }
// }
//
// pub trait Renderer {
//     #[inline]
//     fn render(t: TreeHandle) -> String;
// }
//
// pub struct LeetcodeTreeFormatRenderer;
//
// impl Renderer for LeetcodeTreeFormatRenderer {
//     #[inline]
//     fn render(t: TreeHandle) -> String {
//         super::T(t).to_leetcode_raw()
//     }
// }
//
