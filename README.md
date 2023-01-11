# describe
Describe is a testing toolkit for writing legible, ergonomic unit tests.

# Getting started
Describe exposes one function for creating a new test case, `assert_that`.
```Rust
use describe::assert_that;

// An example function to test.
fn get_answer_to_life() -> u8 {
    42
}

...

// Assert that the answer to life is 42.
assert_that(&get_answer_to_life()).is(&42);
```
