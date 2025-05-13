# Code Artifacts for "Speeding Up Sum-Check Proving"

This repository collects the implementation component of our paper, submitted to Asiacrypt 2025. There are three main repos (included as submodules):

- `arkworks-algebra`: include the code for optimized multiplication of a large field element (in Montgomery form, represented as N limbs of u64's) with `{u64/i64/u128/i128}` elements.
- `jolt`: include the code for small value optimization applied to Spartan
- `smallfield-super-sumcheck`: include the standalone implementation for individual benchmarks

## Cloning the Repository and Building Submodules

To clone this repository and its submodules, follow these steps:

1.  Clone the main repository:
    ```bash
    git clone --recurse-submodules <URL_OF_THIS_REPO>
    cd asiacrypt-2025-submission
    ```
    If you have already cloned the repository without the submodules, you can initialize and update them using:
    ```bash
    git submodule update --init --recursive
    ```

2.  To ensure the submodules are on the correct branches as specified in `.gitmodules` and to pull the latest changes from those branches:
    ```bash
    git submodule sync --recursive
    git submodule update --init --recursive --remote
    ```

## TODO: Testing & Benchmarking

This section outlines the testing and benchmarking procedures for each submodule.

### arkworks-algebra

-   **Testing:**
    -   The following commands run the tests for optimized multiplication in the `ark-ff` crate, specifically targeting operations with `u64`/`i64`/`u128`/`i128` types. These tests use the `bn254` curve features.
        First, navigate to the submodule directory:
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
        First, navigate to the submodule directory:
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
    -   [Instructions for running tests]
-   **Benchmarking:**
    -   [Instructions for running benchmarks]

### smallfield-super-sumcheck

-   **Testing:**
    -   [Instructions for running tests]
-   **Benchmarking:**
    -   [Instructions for running benchmarks]
