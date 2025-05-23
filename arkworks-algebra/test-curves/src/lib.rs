#![no_std]

pub use ark_ff::{self, fields::models::*, FftField, Field, LegendreSymbol, MontFp, PrimeField};

pub use ark_ec::{self, *};

pub use ark_ff_macros::unroll_for_loops;

#[cfg(any(feature = "bls12_381_scalar_field", feature = "bls12_381_curve"))]
pub mod bls12_381;

#[cfg(any(feature = "bls12_381_scalar_field", feature = "ed_on_bls12_381"))]
pub mod ed_on_bls12_381;

#[cfg(feature = "mnt6_753")]
pub mod mnt6_753;

#[cfg(any(
    feature = "mnt4_753_scalar_field",
    feature = "mnt4_753_base_field",
    feature = "mnt4_753_curve"
))]
pub mod mnt4_753;

#[cfg(any(
    feature = "bn384_small_two_adicity_scalar_field",
    feature = "bn384_small_two_adicity_base_field",
    feature = "bn384_small_two_adicity_curve"
))]
pub mod bn384_small_two_adicity;

#[cfg(feature = "secp256k1")]
pub mod secp256k1;

#[cfg(feature = "bn254")]
pub mod bn254;

pub mod fp128;
