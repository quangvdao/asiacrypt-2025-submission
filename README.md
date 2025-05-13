# Code Artifacts for "Speeding Up Sum-Check Proving"

This repository collects the implementation component of our paper, submitted to Asiacrypt 2025. There are three main codebases (now vendored directly in this repository):

- `arkworks-algebra`: includes the code for optimized multiplication of a large field element (in Montgomery form, represented as N limbs of u64's) with `{u64/i64/u128/i128}` elements.
- `jolt`: will include the code for small value optimization applied to Spartan (**coming soon**)
- `smallfield-super-sumcheck`: will include the standalone implementation for individual benchmarks (**coming soon**)

## Repository Structure and Setup

All code dependencies are now included directly in this repository. There are **no submodules** or external Git dependencies. To get started:

1.  Clone this repository as usual:
    ```bash
    git clone <URL_OF_THIS_REPO>
    cd asiacrypt-2025-submission
    ```
2.  No further setup is required. All code is present in the repository.

## TODO: Testing & Benchmarking

This section outlines the testing and benchmarking procedures for each codebase.

### arkworks-algebra

-   **Testing:**
    -   The following commands run the tests for optimized multiplication in the `ark-ff` crate, specifically targeting operations with `u64`/`i64`/`u128`/`i128` types. These tests use the `bn254` curve features.
        First, navigate to the directory:
        ```bash
        cd arkworks-algebra
        ```
        Then, run the specified tests:
        ```bash
        cargo test -p ark-ff --features ark-test-curves/bn254 -- montgomery_backend::test::test_mul_u64_random montgomery_backend::test::test_mul_i64_random montgomery_backend::test::test_mul_u128_random montgomery_backend::test::test_mul_i128_random
        ```
        After running the tests, you can return to the main project directory:
        ```bash
        cd ..
        ```
-   **Benchmarking:**
    -   The benchmarks for these optimized multiplication routines are located in the `ark-test-curves` crate, under the `small_mul` benchmark suite. These benchmarks also use the `bn254` curve features.
        First, navigate to the directory:
        ```bash
        cd arkworks-algebra
        ```
        Then, run the benchmark:
        ```bash
        cargo bench -p ark-test-curves --bench small_mul --features bn254
        ```
        Benchmark results are typically generated in the `target/criterion/report/index.html` file within the `arkworks-algebra` directory.
        After running the benchmarks, you can return to the main project directory:
        ```bash
        cd ..
        ```
    - Expectation for the benchmark: You should see that the `mul_u64` function should be around ~2.5x faster than the `standard mul (Fr * Fr)` function. The `mul_i64` function is slightly more expensive than `mul_u64`. Finally, the `mul_u128` takes slightly less time than standard mul, while `mul_i128` takes slightly more time. These results were obtained on a M4 Macbook Air.

### jolt

-   **Testing:**
    -   [Coming soon]
-   **Benchmarking:**
    -   [Coming soon]

### smallfield-super-sumcheck

-   **Testing:**
    -   [Coming soon]
-   **Benchmarking:**
    -   [Coming soon]
