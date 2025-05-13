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
    -   [Instructions for running tests]
-   **Benchmarking:**
    -   [Instructions for running benchmarks]

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
