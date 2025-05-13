#[cfg(feature = "bn254_base_field")]
pub mod fq;
#[cfg(feature = "bn254_base_field")]
pub use fq::*;

#[cfg(feature = "bn254_scalar_field")]
pub mod fr;
#[cfg(feature = "bn254_scalar_field")]
pub use fr::*;

#[cfg(feature = "bn254")] // Use the main bn254 feature
pub mod g1;
#[cfg(feature = "bn254")] // Use the main bn254 feature
pub use g1::*;

// TODO: Define G2, GT, Pairing for BN254 similarly if needed

#[cfg(test)]
mod test; // Renamed from tests to test.rs
