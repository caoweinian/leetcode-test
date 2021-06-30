// //! 2021.6.30; This module is not finished yet.
//
// use super::TreeHandle;
// use std::collections::HashSet;
// use std::time::Duration;
//
// pub type Bone = Vec<bool>;
//
// #[derive(Debug)]
// pub enum Subset {
//     Default,
//     FixedLen(u32),
//     // of len *
//     FixedHeight(u32),
//     // of height *
//     SingleList(u32),
//     // of height no more than *
//     FullShape(u8),
//     // of height no more than *
//     HeapShape(u32),
//     // of len no more than *
//     CompleteShape(u32),
//     // of len no more than *
//     Shape(Vec<Bone>), // of shapes specified in *
// }
//
// #[derive(Debug)]
// pub enum StopWhen {
//     StructureDrained,
//     TriedTimes(u64),
//     TimesUp(Duration),
//     GotNums(u32),
//     GotRate(f64),
// }
//
// #[derive(Debug)]
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
// pub enum GenError {}
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
//     /* priv */ unsafe fn gen_unchecked(self) -> Vec<TreeHandle> {
//         unimplemented!()
//     }
//
//     pub fn test(&self) -> Result<(), GenError> {
//         unimplemented!()
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
//     pub fn run(self) -> Result<FinalFilter, GenError> {
//         let mut v = vec![2, 3, 4];
//         unimplemented!()
//     }
// }
//
// pub struct FinalFilter(Vec<TreeHandle>);
//
// impl FinalFilter {
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
// pub trait BoneRenderer {
//     fn render(t: TreeHandle) -> String {
//         unimplemented!()
//     }
// }
//
// pub struct LeetcodeRenderer;
//
// impl BoneRenderer for LeetcodeRenderer {}
//
// #[inline]
// pub fn fmt<T>(t: TreeHandle, r: T) -> String
//     where T: BoneRenderer {
//     T::render(t)
// }
//
// #[inline]
// pub fn fmt_leetcode(t: TreeHandle) -> String {
//     LeetcodeRenderer::render(t)
// }
//
