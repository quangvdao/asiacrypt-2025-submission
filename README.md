# Code Artifacts for "Speeding Up Sum-Check Proving"

This repository collects the implementation component of our paper, submitted to Asiacrypt 2025. There are three main codebases (now vendored directly in this repository):

- `arkworks-algebra`: includes the code for optimized multiplication of a large field element (in Montgomery form, represented as N limbs of u64's) with `{u64/i64/u128/i128}` elements.
- `jolt`: will include the code for small value optimization applied to Spartan
- `smallfield-super-sumcheck`: will include the standalone implementation for individual benchmarks

## Repository Structure and Setup

All code dependencies are now included directly in this repository. There are **no submodules** or external Git dependencies. To get started:

1.  Clone this repository as usual:
    ```bash
    git clone <URL_OF_THIS_REPO>
    cd asiacrypt-2025-submission
    ```
2.  No further setup is required. All code is present in the repository.

## Benchmarking Instructions

This section outlines the benchmarking procedures for each codebase.

### arkworks-algebra

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

- This benchmark evaluates the performance of Spartan's first sumcheck, including variants with optimizations like Gruen and Small Value Optimization (SVO). It uses the `sha2-chain-guest` program with varying iteration counts.
    First, navigate to the `jolt-core` directory within the `jolt` codebase:
    ```bash
    cd jolt/jolt-core
    ```
    Then, run the benchmark:
    ```bash
    cargo bench -p jolt-core --bench spartan_first_sumcheck
    ```
    Benchmark results are typically generated in the `target/criterion/report/index.html` file within the `jolt/jolt-core` directory.
    After running the benchmarks, you can return to the main project directory:
    ```bash
    cd ../..
    ```

### smallfield-super-sumcheck


