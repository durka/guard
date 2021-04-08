/// Match a pattern to an expression, binding identifiers in the calling scope. Panic if the
/// match fails.
///
/// Supported syntax:
///
/// - let `pattern` = `rhs`
///
/// Inputs:
///
/// - `rhs`: expression to match against the pattern
/// - `pattern`: pattern. See [`guard`](crate#limitations) for details on which patterns
///   are accepted.
///
/// Note that pattern guards are not supported.
///
/// ```
/// #[macro_use] extern crate guard;
/// guard_unwrap!(let Some(foo) = Some(42));
/// assert_eq!(foo, 42);
/// ```
///
/// Here's an example of a failing match that causes [`guard_unwrap`] to panic.
///
/// ``` should_panic
/// #[macro_use] extern crate guard;
/// guard_unwrap!(let Option::None = Some(42));
/// ```
///
/// Note that `Option::None` is used instead of `None` to work around the limitations
/// of accepted patterns. See [`guard`](crate#limitations) for details.
///
/// Also note that this macro is mostly provided for destructuring enums in tests.
/// In production code it's usually better to handle all variants of enums explicitly.
#[macro_export]
macro_rules! guard_unwrap {
    ($($input:tt)*) => {
        $crate::guard!(
            $($input)* else { $crate::guard_unwrap_panic!($($input)*) }
        );
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! guard_unwrap_panic {
    (let $pattern:pat = $expression:expr) => {
        panic!(
            "assertion failed: `let {} = {}`",
            stringify!($pattern),
            stringify!($expression),
        )
    };
}

#[cfg(test)]
mod test {
    #[test]
    fn should_match() {
        let val: Option<()> = None;
        guard_unwrap!(let Option::None = val);
    }

    #[test]
    fn should_bind() {
        let val = Some(42);
        guard_unwrap!(let Some(n) = val);
        assert_eq!(n, 42);
    }

    #[test]
    #[should_panic]
    fn should_panic() {
        let val: Option<()> = None;
        guard_unwrap!(let Some(_) = val);
    }

    #[test]
    #[should_panic(expected = "Some(_)")]
    fn panic_message_should_include_pattern() {
        let val: Option<()> = None;
        guard_unwrap!(let Some(_) = val);
    }

    #[test]
    #[should_panic(expected = "val")]
    fn panic_message_should_include_matched_expression() {
        let val: Option<()> = None;
        guard_unwrap!(let Some(_) = val);
    }

    #[test]
    #[should_panic(expected = "assertion failed: `let Some(_) = foo(bar)`")]
    fn should_have_nice_panic_message() {
        let bar = true;
        fn foo(_: bool) -> Option<()> {
            None
        }
        guard_unwrap!(let Some(_) = foo(bar));
    }
}
