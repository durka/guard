#![cfg_attr(all(test, feature = "nightly"), feature(braced_empty_structs,
                                                    box_syntax,
                                                    box_patterns,
                                                    slice_patterns,
                                                    advanced_slice_patterns
                                                   ))]

#![cfg_attr(feature = "debug", feature(trace_macros))]

//!  This crate exports a macro which implements most of [RFC 1303](https://github.com/rust-lang/rfcs/pull/1303) (a "let-else" or "guard" expression as you can find in Swift).
//!
//! The syntax proposed in the RFC was `if !let PAT = EXPR { BODY }` or `let PAT = EXPR else { BODY }` (where `BODY` _must_ diverge). Due to implementation details, this macro has the rather awkward syntax `guard!({ BODY } unless EXPR => PAT)`. Alternative syntaxes may be added in the future.
//!
//! Example usage:
//!
//! ```rust
//! #[macro_use] extern crate guard;
//! use std::env;
//! 
//! fn main() {
//!     // read configuration from a certain environment variable
//!     // do nothing if the variable is missing
//!     guard!({ return } unless env::var("FOO") => Ok(foo));
//! 
//!     println!("FOO = {}", foo);
//! }
//! ```
//!
//! ## Limitations
//! 
//! 1. Expressions in the pattern are _not_ supported. This is a limitation of the current Rust macro system -- I'd like to say "parse an identifier in this position, but if that fails try parsing an expression" but this is is impossible; I can only test for _specific_ identifiers. It's easy to get around this restriction: use a pattern guard (as in `match`) instead.
//! 2. Empty, un-namespaced enum variants and structs cause the expansion to fail, because the macro thinks they are identifiers. It's possible to get around this as well, though an open PR is aiming to take away the easiest workaround:
//!    a. For empty enum variants, use `Empty(..)` until [#29383](rust-lang/rust#29383) lands, after that include the enum name as in `Enum::Empty`.
//!    b. For unit-like structs, use `Empty(..)` until [#29383](rust-lang/rust#28393) lands, after that namespace it as in `namespace::Empty`, or use `Empty{}` (requires `#![feature(braced_empty_structs)]`).
//! 3. `PAT` cannot be irrefutable. This is the same behavior as `if let` and `match`, and it's useless to write a guard with an irrefutable pattern anyway (you can just use `let`), so this shouldn't be an issue. This is slightly more annoying than it could be due to limitation #1. Nonetheless, if [#14252](rust-lang/rust#14252) is ever fixed, irrefutable patterns could be allowed by inserting a no-op pattern guard into the expansion.

#[cfg(feature = "debug")]
trace_macros!(true);

#[doc(hidden)]
#[macro_export]
macro_rules! __guard_impl {
    (@as_stmt $s:stmt) => { $s };

    (@collect () -> (($($imms:ident)*) ($($muts:ident)*)), [($($guard:tt)*) ($($pattern:tt)*) ($rhs:expr) ($diverge:expr)]) => {
        // FIXME after #29850 lands, try putting #[allow(unused_mut)] in here somewhere
        __guard_impl!(@as_stmt
               let ($($imms,)* $(mut $muts,)*) = match $rhs {
                                                    $($pattern)* $($guard)*
                                                                 // ^ this defeats the "unreachable pattern" error
                                                        => {
                                                            $($muts = $muts;)* // this defeats the "unused mut" warning
                                                            ($($imms,)* $($muts,)*)
                                                        },

                                                    _ => { $diverge },
                                                 }
              )
    };

    (@collect (($($inside:tt)*) $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        __guard_impl!(@collect ($($inside)* $($tail)*) -> $idents, $thru)
    };
    (@collect ({$($inside:tt)*} $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        __guard_impl!(@collect ($($inside)* $($tail)*) -> $idents, $thru)
    };
    (@collect ([$($inside:tt)*] $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        __guard_impl!(@collect ($($inside)* $($tail)*) -> $idents, $thru)
    };
    (@collect (, $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        __guard_impl!(@collect ($($tail)*) -> $idents, $thru)
    };
    (@collect (.. $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        __guard_impl!(@collect ($($tail)*) -> $idents, $thru)
    };
    (@collect (@ $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        __guard_impl!(@collect ($($tail)*) -> $idents, $thru)
    };
    (@collect (_ $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        __guard_impl!(@collect ($($tail)*) -> $idents, $thru)
    };
    (@collect (& $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        __guard_impl!(@collect ($($tail)*) -> $idents, $thru)
    };
    (@collect (:: $pathend:ident $($tail:tt)*) -> $idents:tt, $thru:tt) => { // due to #27832 this has to be before the ident arms instead of near the $pathcomp arm
        __guard_impl!(@collect ($($tail)*) -> $idents, $thru)
    };
    (@collect (| $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        __guard_impl!(@collect () -> $idents, $thru) // all the bindings on either side of | must be the same, so we don't have to parse the rest
    };
    (@collect (if $($tail:tt)*) -> $idents:tt, [$guard:tt $($rest:tt)*]) => {
        __guard_impl!(@collect () -> $idents, [() $($rest)*])
    };
    (@collect ($id:ident: $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        __guard_impl!(@collect ($($tail)*) -> $idents, $thru)
    };
    (@collect ($pathcomp:ident :: $pathend:ident $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        __guard_impl!(@collect ($($tail)*) -> $idents, $thru)
    };
    (@collect ($id:ident ($($inside:tt)*) $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        __guard_impl!(@collect ($($inside)* $($tail)*) -> $idents, $thru)
    };
    (@collect ($id:ident {$($inside:tt)*} $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        __guard_impl!(@collect ($($inside)* $($tail)*) -> $idents, $thru)
    };
    (@collect (ref mut $id:ident $($tail:tt)*) -> (($($imms:ident)*) $muts:tt), $thru:tt) => {
        __guard_impl!(@collect ($($tail)*) -> (($($imms)* $id) $muts), $thru)
    };
    (@collect (ref $id:ident $($tail:tt)*) -> (($($imms:ident)*) $muts:tt), $thru:tt) => {
        __guard_impl!(@collect ($($tail)*) -> (($($imms)* $id) $muts), $thru)
    };
    (@collect (mut $id:ident $($tail:tt)*) -> ($imms:tt ($($muts:ident)*)), $thru:tt) => {
        __guard_impl!(@collect ($($tail)*) -> ($imms ($($muts)* $id)), $thru)
    };
    (@collect (box $id:ident $($tail:tt)*) -> (($($imms:ident)*) $muts:tt), $thru:tt) => {
        __guard_impl!(@collect ($($tail)*) -> (($($imms)* $id) $muts), $thru)
    };
    (@collect ($id:ident $($tail:tt)*) -> (($($imms:ident)*) $muts:tt), $thru:tt) => {
        __guard_impl!(@collect ($($tail)*) -> (($($imms)* $id) $muts), $thru)
    };

    ({ $($diverge:tt)* } unless $rhs:expr => $($pattern:tt)*) => {
        __guard_impl!(@collect ($($pattern)*) -> (() ()), [() ($($pattern)*) ($rhs) ({$($diverge)*})])
        // FIXME once #14252 is fixed, put "if true" in as the default guard to defeat E0008
    }
}

/// Match a pattern to an expression, binding identifiers in the calling scope. Diverge if the
/// match fails.
///
/// Inputs:
/// - `diverge`: expression which is run if the match fails. Must diverge, or you will get a "match
/// arms have incompatible types" error.
/// - `rhs`: expression to match against the pattern
/// - `pattern`: pattern. Most patterns are allowed, with a few limitations. See the module
/// documentation for details.
#[macro_export]
macro_rules! guard {
    ({ $($diverge:tt)* } unless $rhs:expr => $($pattern:tt)*) => {
        __guard_impl!({ $($diverge)* } unless $rhs => $($pattern)*)
    }
}

#[cfg(test)]
mod tests {
    #[derive(Debug)]
    enum Stuff {
        A(Option<i32>, Option<i32>),
        B { foo: Result<i32, i32>, bar: i32 },
        C(i32),
        D
    }

    #[derive(Copy, Clone)] struct Point { x: i32, y: i32 }
    struct Person { name: Option<String> }

    #[test]
    fn various() {
        let origin = Point { x: 0, y: 0 };
        let p = Some(Person { name: Some("Steve".to_owned()) });
        let opt = Stuff::A(Some(42), Some(43));
        let copt = Stuff::C(42);
        let dopt = Stuff::D;
        let mut thing = Stuff::B { foo: Ok(44), bar: 45 };

        guard!({ return } unless Some(&42) => Some(&x));                                println!("{}", x);

        guard!({ return } unless Stuff::C(42) => Stuff::B { bar, .. } | Stuff::C(bar)); println!("{}", bar);

        guard!({ return } unless Some(42) => Some(x));                                  println!("{}", x);

        guard!({ return } unless Some(origin) => Some(Point { x, y }));                 println!("{} {}", x, y);

        guard!({ return } unless Some(origin) => Some(Point { x: x1, y: y1 }));         println!("{} {}", x1, y1);

        guard!({ return } unless Some(origin) => Some(Point { x, .. }));                println!("{}", x);

        guard!({ return } unless Some(origin) => Some(Point { y: y1, .. }));            println!("{}", y1);

        // closest we can get to Point { x, y: 0 }
        guard!({ return } unless origin => Point { x, y: _y } if _y == 0);              println!("{}", x);

        guard!({ return } unless p => Some(Person { name: ref x @ Some(_), .. }));      println!("{:?}", x);

        guard!({ return } unless (Some(42), Some(43)) => (Some(x), Some(y)));           println!("{} {}", x, y);

        guard!({ return } unless opt => Stuff::A(Some(x), Some(y)));                    println!("{} {}", x, y);
        
        guard!({ return } unless thing => Stuff::B { foo: Ok(ref mut x), .. });         *x += 1; println!("{}", x);

        guard!({ return } unless thing => self::Stuff::B { foo: Ok(mut x), .. });       x *= 2; println!("{}", x);
        
        guard!({ return } unless copt => Stuff::C(_));

        guard!({ return } unless dopt => self::Stuff::D);
    }

    #[cfg(not(feature = "nightly"))]
    #[test]
    fn empty() {
        use self::Stuff::D;
        struct Empty;

        let dopt = D;

        guard!({ return } unless dopt => D(..));
        guard!({ return } unless Some(Empty) => Some(Empty(..)));
    }

    #[cfg(feature = "nightly")]
    #[test]
    fn empty() {
        use self::Stuff::D;
        struct Empty;

        let dopt = D;

        guard!({ return } unless dopt => D(..));
        guard!({ return } unless Some(Empty) => Some(Empty{}));
    }

    #[cfg(feature = "nightly")]
    #[test]
    fn nightly() {
        // box patterns
        let foo = (box 42, [1, 2, 3]);
        guard!({ return } unless Some(foo) => Some((box x, _)));                           println!("{}", x);

        // slice patterns
        let foo = (box 42, [1, 2, 3]);
        guard!({ return } unless Some(foo) => Some((_, [a, b, c])));                       println!("{} {} {}", a, b, c);
        
        // advanced slice patterns
        let foo = (box 42, [1, 2, 3]);
        guard!({ return } unless Some((foo.0, &foo.1)) => Some((box x, &[head, tail..]))); println!("{} {} {:?}", x, head, tail);
    }
}

