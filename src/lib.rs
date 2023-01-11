#![allow(clippy::wrong_self_convention)]

use std::{borrow::Borrow, fmt::Debug};

#[derive(Debug, PartialEq)]
pub struct PanickingTestCase<'a, T>
where
    T: Debug + ?Sized,
{
    value: &'a T,
}

impl<'a, T> PanickingTestCase<'a, T>
where
    T: Debug + ?Sized,
{
    /// Maps the value of this test-case to another value.
    ///
    /// # Example
    /// ```
    /// use describe::assert_that;
    ///
    /// #[derive(Debug)]
    /// struct Foo {
    ///     bar: u8,
    /// }
    ///
    /// assert_that(&Foo { bar: 42 }).map(|foo| &foo.bar).is(&42);
    /// // need to be able to construct PanickingTestCase with owned value for this to work
    /// // assert_that("chocolate chip").map(|s| s.chars().rev().collect::<String>()).is("pihc etalocohc");
    /// ```
    pub fn map<U, F>(self, f: F) -> PanickingTestCase<'a, U>
    where
        F: Fn(&'a T) -> &'a U,
        U: Debug,
    {
        PanickingTestCase {
            value: f(self.value),
        }
    }
}

/// Constructs a PanickingAssertion over the given value.
///
/// # Example
/// ```
/// use describe::assert_that;
///
/// fn get_answer_to_life() -> u8 {
///     42
/// }
///
/// assert_that(&get_answer_to_life()).is(&42);
/// ```
pub fn assert_that<T>(value: &T) -> PanickingTestCase<'_, T>
where
    T: Debug + ?Sized,
{
    PanickingTestCase { value }
}

impl<'a> PanickingTestCase<'a, bool> {
    /// Asserts that the test-case value is true.
    ///
    /// # Example
    /// ```
    /// use describe::assert_that;
    ///
    /// fn is_even(x: u8) -> bool {
    ///     x % 2 == 0
    /// }
    ///
    /// assert_that(&is_even(42)).is_true();
    /// ```
    pub fn is_true(self) -> PanickingTestCase<'a, bool> {
        assert!(self.value);
        self
    }

    /// Asserts that the test-case value is false.
    ///
    /// # Example
    /// ```
    /// use describe::assert_that;
    ///
    /// fn is_odd(x: u8) -> bool {
    ///     x % 2 == 1
    /// }
    ///
    /// assert_that(&is_odd(42)).is_false();
    /// ```
    pub fn is_false(self) -> PanickingTestCase<'a, bool> {
        assert!(!self.value);
        self
    }
}

impl<'a, T> PanickingTestCase<'a, T>
where
    T: Debug + ?Sized,
{
    /// Asserts that the test-case value is equal to the given value.
    ///
    /// # Example
    /// ```
    /// use describe::assert_that;
    ///
    /// fn get_answer_to_life() -> u8 {
    ///     42
    /// }
    ///
    /// assert_that(&get_answer_to_life()).is(&42);
    /// ```
    pub fn is<U>(self, other: U) -> PanickingTestCase<'a, T>
    where
        &'a T: PartialEq<U>,
        U: Debug,
    {
        assert!(
            self.value == other,
            "{:?} should be {:?}",
            self.value,
            other.borrow()
        );
        self
    }

    /// Asserts that the test-case value is *not* equal to the given value.
    ///
    /// # Example
    /// ```
    /// use describe::assert_that;
    ///
    /// fn get_answer_to_life() -> u8 {
    ///     42
    /// }
    ///
    /// assert_that(&get_answer_to_life()).is_not(&23);
    /// ```
    pub fn is_not<U>(self, other: U) -> PanickingTestCase<'a, T>
    where
        &'a T: PartialEq<U>,
        U: Debug,
    {
        assert!(
            self.value != other,
            "{:?} should not be {:?}",
            self.value,
            other.borrow()
        );
        self
    }
}

impl<'a, T> PanickingTestCase<'a, T>
where
    T: Debug,
{
    /// Asserts that the test-case value is greater than the given value.
    ///
    /// # Example
    /// ```
    /// use describe::assert_that;
    ///
    /// fn get_answer_to_life() -> u8 {
    ///     42
    /// }
    ///
    /// assert_that(&get_answer_to_life()).is_gt(&40);
    /// ```
    pub fn is_gt<U>(self, value: U) -> PanickingTestCase<'a, T>
    where
        &'a T: PartialOrd<U>,
    {
        assert!(self.value > value);
        self
    }

    /// Asserts that the test-case value is less than the given value.
    ///
    /// # Example
    /// ```
    /// use describe::assert_that;
    ///
    /// fn get_answer_to_life() -> u8 {
    ///     42
    /// }
    ///
    /// assert_that(&get_answer_to_life()).is_lt(&44);
    /// ```
    pub fn is_lt<U>(self, value: U) -> PanickingTestCase<'a, T>
    where
        &'a T: PartialOrd<U>,
    {
        assert!(self.value < value);
        self
    }

    /// Asserts that the test-case value is greater than or equal to the given value.
    ///
    /// # Example
    /// ```
    /// use describe::assert_that;
    ///
    /// fn get_answer_to_life() -> u8 {
    ///     42
    /// }
    ///
    /// assert_that(&get_answer_to_life()).is_ge(&40);
    /// assert_that(&get_answer_to_life()).is_ge(&42);
    /// ```
    pub fn is_ge<U>(self, value: U) -> PanickingTestCase<'a, T>
    where
        &'a T: PartialOrd<U>,
    {
        assert!(self.value >= value);
        self
    }

    /// Asserts that the test-case value is less than or equal to the given value.
    ///
    /// # Example
    /// ```
    /// use describe::assert_that;
    ///
    /// fn get_answer_to_life() -> u8 {
    ///     42
    /// }
    ///
    /// assert_that(&get_answer_to_life()).is_le(&44);
    /// assert_that(&get_answer_to_life()).is_le(&42);
    /// ```
    pub fn is_le<U>(self, value: U) -> PanickingTestCase<'a, T>
    where
        &'a T: PartialOrd<U>,
    {
        assert!(self.value <= value);
        self
    }
}

impl<'a, T> PanickingTestCase<'a, T>
where
    &'a T: AsRef<str>,
    T: Debug + ?Sized, // remove Sized in case T is str
{
    /// Asserts that the test-case string contains the given substring.
    ///
    /// # Example
    /// ```
    /// use describe::assert_that;
    ///
    /// // assert_that("chocolate chip").contains("chocolate");
    /// ```
    pub fn contains<S>(self, sub: S)
    where
        S: AsRef<str>,
    {
        let s: &str = self.value.as_ref();
        assert!(s.contains(sub.as_ref()));
    }
}

impl<'a, T> PanickingTestCase<'a, T>
where
    T: Debug + std::panic::RefUnwindSafe + ?Sized,
{
    /// Asserts that the given function returns `true` when passed the test-case value.
    ///
    /// # Example
    /// ```
    /// use describe::assert_that;
    ///
    /// fn is_longer_than_ten(s: &str) -> bool {
    ///     s.len() > 10
    /// }
    ///
    /// assert_that("chocolate chip").satisfies(is_longer_than_ten);
    /// ```
    pub fn satisfies<F>(self, f: F) -> PanickingTestCase<'a, T>
    where
        F: FnOnce(&'a T) -> bool,
    {
        let result = f(self.value);
        assert!(result);
        self
    }

    /// Asserts that the given function panicks when passed the test-case value.
    ///
    /// # Example
    /// ```
    /// use describe::assert_that;
    ///
    /// assert_that(&None).panicks_in(|value| value.unwrap());
    /// ```
    pub fn panicks_in<F>(self, f: F) -> PanickingTestCase<'a, T>
    where
        F: FnOnce(&'a T) + std::panic::UnwindSafe,
    {
        match std::panic::catch_unwind(|| f(self.value)) {
            Ok(_) => panic!(
                "The given function should have panicked with argument '{:?}'",
                self.value
            ),
            Err(_) => self,
        }
    }
}
