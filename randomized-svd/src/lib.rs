//! Randomized SVD — a Rust implementation of the subspace iteration algorithm
//! from Halko, Martinsson, Tropp (2011).

pub mod matrix;
pub mod error;
pub mod svd;
pub mod eigen;

pub use svd::{randomized_svd, low_rank_approx, svd_errors, RandSVDResult};
pub use svd::{per_svd, PerSVDParams, PerSVDShift};
