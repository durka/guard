#![cfg_attr(all(test, feature = "nightly"), feature(stmt_expr_attributes,
                                                    braced_empty_structs,
                                                    box_syntax,
                                                    box_patterns,
                                                    slice_patterns,
                                                    advanced_slice_patterns
                                                   ))]

#![cfg_attr(feature = "debug", feature(trace_macros))]

//!  This crate exports a macro which implements most of [RFC 1303](https://github.com/rust-lang/rfcs/pull/1303) (a "let-else" or "guard"
//!  expression as you can find in Swift).
//!
//! The syntax proposed in the RFC was `if !let PAT = EXPR { BODY }` or `let PAT = EXPR else { BODY }` (where `BODY` _must_ diverge).
//!
//! 1. The newer syntax, `guard!(let PAT = EXPR else { BODY })`. If added to the language, this
//!    would be ambiguous (consider `let foo = if bar { baz() } else { quux() }` -- is it a `let`
//!    statement or a `let else` statement?), however in the context of this macro there is no
//!    ambiguity because only `let else` statements are allowed.
//!
//!    A variation suggested in the RFC discussion, `guard!(let PAT else { BODY } = EXPR)`, is also
//!    supported.
//! 2. The older syntax, `guard!({ BODY } unless EXPR => PAT)`. This should be a little faster to
//!    compile than the newer syntax, which requires an initial loop through the token stream to
//!    separate the pattern, expression and body (the normal `macro_rules!` syntax is not quite
//!    powerful enough).
//!
//! Example usage:
//!
//! ```rust
#![cfg_attr(feature = "nightly", doc = "#![feature(stmt_expr_attributes)]")]
//! #[macro_use] extern crate guard;
//!
//! # use std::env;
//! # fn main() {
//! // read configuration from a certain environment variable
//! // do nothing if the variable is missing
//! guard!(let Ok(foo) = env::var("FOO")
//!        else { return });
//! 
//! println!("FOO = {}", foo);
//! # }
//! ```
//!
//! Unlike `if let`, pattern guards are allowed in PAT, and, if using the new syntax, unlike `match`
//! you don't get a "cannot bind by-move" error:
//!
//! ```rust
#![cfg_attr(feature = "nightly", doc = "# #![feature(stmt_expr_attributes)]")]
//! # #[macro_use] extern crate guard;
//! # use std::env;
//! # fn main() {
//! guard!(let Ok(foo) if foo.starts_with("bar") = env::var("FOO")
//!        else { return });
//! # println!("FOO = {}", foo);
//! # }
//! ```
//!
//! The BODY expression is enforced to be diverging at compile time (with the naive expansion to
//! `if let` or `match`, it would be allowed to return fallback values for the bindings instead of
//! diverging, which would violate the semantics of the guard statement, namely that code after it
//! never executes if the pattern doesn't match).
//!
//! ## Limitations
//! 
//! 1. Expressions in the pattern are _not_ supported. This is a limitation of the current Rust
//!    macro system -- I'd like to say "parse an identifier in this position, but if that fails try
//!    parsing an expression" but this is is impossible; I can only test for _specific_
//!    identifiers. It's easy to get around this restriction: use a pattern guard (as in `match`)
//!    instead.
//! 2. Empty, un-namespaced enum variants and structs cause the expansion to fail, because the
//!    macro thinks they are identifiers. It's possible to get around this as well, though an open
//!    PR is aiming to take away the easiest workaround:
//!
//!     a. For empty enum variants, use `Empty(..)` until
//!     [#29383](https://github.com/rust-lang/rust/issues/29383) lands, after that include the enum
//!     name as in `Enum::Empty`.
//!     b. For unit-like structs, use `Empty(..)` until
//!     [#29383](https://github.com/rust-lang/rust/issues/29383) lands, after that namespace it as
//!     in `namespace::Empty`, or use `Empty{}` (requires `#![feature(braced_empty_structs)]`).
//! 3. `PAT` cannot be irrefutable. This is the same behavior as `if let` and `match`, and it's
//!    useless to write a guard with an irrefutable pattern anyway (you can just use `let`), so
//!    this shouldn't be an issue. This is slightly more annoying than it could be due to
//!    limitation #1. Nonetheless, if [#14252](https://github.com/rust-lang/rust/issues/14252) is
//!    ever fixed, irrefutable patterns could be allowed by inserting a no-op pattern guard into
//!    the expansion.

#[cfg(feature = "debug")]
trace_macros!(true);

/// Uninhabitable type used to make an error message
pub enum LetElseBodyMustDiverge {}

#[cfg(not(feature = "nightly"))]
#[doc(hidden)]
#[macro_export]
macro_rules! __guard_output {
    ((($($imms:ident)*) ($($muts:ident)*)), [($($guard:tt)*) ($($pattern:tt)*) ($rhs:expr) ($diverge:expr)]) => {
        __guard_impl!(@as_stmt
               let ($($imms,)* $(mut $muts,)*) = match $rhs {
                                                   $($pattern)* => {
                                                       if $($guard)* { // move the guard inside to avoid "cannot bind by-move"
                                                           $($muts = $muts;)* // this defeats the "unused mut" warning
                                                           ($($imms,)* $($muts,)*)
                                                       } else {
                                                           let _: $crate::LetElseBodyMustDiverge = $diverge;
                                                           loop {}
                                                       }
                                                   },

                                                   _ => {
                                                       let _: $crate::LetElseBodyMustDiverge = $diverge;
                                                       loop {}
                                                   },
               }
              )
    };
}

#[cfg(feature = "nightly")]
#[doc(hidden)]
#[macro_export]
macro_rules! __guard_output {
    ((($($imms:ident)*) ($($muts:ident)*)), [($($guard:tt)*) ($($pattern:tt)*) ($rhs:expr) ($diverge:expr)]) => {
        __guard_impl!(@as_stmt
               let ($($imms,)* $(mut $muts,)*) = #[allow(unused_mut)]
                                                 match $rhs {
                                                   $($pattern)* => {
                                                       if $($guard)* { // move the guard inside to avoid "cannot bind by-move"
                                                           ($($imms,)* $($muts,)*)
                                                       } else {
                                                           let _: $crate::LetElseBodyMustDiverge = $diverge;
                                                           loop {}
                                                       }
                                                   },

                                                   _ => {
                                                       let _: $crate::LetElseBodyMustDiverge = $diverge;
                                                       loop {}
                                                   },
               }
              )
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __guard_impl {
    // 0. cast a series of token trees to a statement
    (@as_stmt $s:stmt) => { $s };

    // 1. output stage
    (@collect () -> $($rest:tt)*) => {
        __guard_output!($($rest)*)
    };


    // 2. identifier collection stage
    //      The pattern is scanned destructively. Anything that looks like a capture (including
    //      false positives, like un-namespaced/empty structs or enum variants) is copied into the
    //      appropriate identifier list. Irrelevant symbols are discarded. The scanning descends
    //      recursively into bracketed structures.

    // unwrap brackets and prepend their contents to the pattern remainder, in case there are captures inside
    (@collect (($($inside:tt)*) $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        __guard_impl!(@collect ($($inside)* $($tail)*) -> $idents, $thru)
    };
    (@collect ({$($inside:tt)*} $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        __guard_impl!(@collect ($($inside)* $($tail)*) -> $idents, $thru)
    };
    (@collect ([$($inside:tt)*] $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        __guard_impl!(@collect ($($inside)* $($tail)*) -> $idents, $thru)
    };

    // discard irrelevant symbols
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

    // ignore generic parameters
    (@collect (:: <$($generic:tt),*> $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        __guard_impl!(@collect ($($tail)*) -> $idents, $thru)
    };
    // a path can't be a capture, and a path can't end with ::, so the ident after :: is never a capture
    (@collect (:: $pathend:ident $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        __guard_impl!(@collect ($($tail)*) -> $idents, $thru)
    };

    // alternative patterns may be given with | as long as the same captures (including type) appear on each side
    // due to this property, if we see a | we've already parsed all the captures and can simply stop
    (@collect (| $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        __guard_impl!(@collect () -> $idents, $thru) // discard the rest of the pattern, proceed to output stage
    };

    // an explicitly provided pattern guard replaces the default, if there was one
    (@collect (if $($tail:tt)*) -> $idents:tt, [$guard:tt $($rest:tt)*]) => {
        __guard_impl!(@collect () -> $idents, [($($tail)*) $($rest)*])
    };

    // throw away some identifiers that do not represent captures
    
    // box destructuring
    (@collect (box $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        __guard_impl!(@collect ($($tail)*) -> $idents, $thru)
    };

    // an ident followed by a colon is the name of a structure member
    (@collect ($id:ident: $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        __guard_impl!(@collect ($($tail)*) -> $idents, $thru)
    };
    // paths do not represent captures
    (@collect ($pathcomp:ident :: $pathend:ident $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        __guard_impl!(@collect ($($tail)*) -> $idents, $thru)
    };
    // an ident followed by parentheses is the name of a tuple-like struct or enum variant
    // (unwrap the parens to parse the contents)
    (@collect ($id:ident ($($inside:tt)*) $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        __guard_impl!(@collect ($($inside)* $($tail)*) -> $idents, $thru)
    };
    // an ident followed by curly braces is the name of a struct or struct-like enum variant
    // (unwrap the braces to parse the contents)
    (@collect ($id:ident {$($inside:tt)*} $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        __guard_impl!(@collect ($($inside)* $($tail)*) -> $idents, $thru)
    };

    // actually identifier collection happens here!

    // capture by mutable reference!
    (@collect (ref mut $id:ident $($tail:tt)*) -> (($($imms:ident)*) $muts:tt), $thru:tt) => {
        __guard_impl!(@collect ($($tail)*) -> (($($imms)* $id) $muts), $thru)
    };
    // capture by immutable reference!
    (@collect (ref $id:ident $($tail:tt)*) -> (($($imms:ident)*) $muts:tt), $thru:tt) => {
        __guard_impl!(@collect ($($tail)*) -> (($($imms)* $id) $muts), $thru)
    };
    // capture by move into mutable binding!
    (@collect (mut $id:ident $($tail:tt)*) -> ($imms:tt ($($muts:ident)*)), $thru:tt) => {
        __guard_impl!(@collect ($($tail)*) -> ($imms ($($muts)* $id)), $thru)
    };
    // capture by move into an immutable binding!
    (@collect ($id:ident $($tail:tt)*) -> (($($imms:ident)*) $muts:tt), $thru:tt) => {
        __guard_impl!(@collect ($($tail)*) -> (($($imms)* $id) $muts), $thru)
    };

    // 3. splitting (for new syntax)

    // done with pattern (and it's LPED=X)
    (@split (else { $($diverge:tt)* } = $($tail:tt)*) -> ($pat:tt $guard:tt)) => {
        __guard_impl!(@collect $pat -> (() ()), [$guard $pat ($($tail)*) ({ $($diverge)* })])
    };

    // done with pattern (and it's LP=XED)
    (@split (= $($tail:tt)*) -> ($pat:tt $guard:tt)) => {
        __guard_impl!(@split expr ($($tail)*) -> ($pat $guard ()))
    };

    // found a guard in the pattern
    (@split (if $($tail:tt)*) -> ($pat:tt $guard:tt)) => {
        __guard_impl!(@split guard ($($tail)*) -> ($pat ()))
    };

    // done with guard (and it's LP=XED)
    (@split guard (= $($tail:tt)*) -> ($pat:tt $guard:tt)) => {
        __guard_impl!(@split expr ($($tail)*) -> ($pat $guard ()))
    };

    // done with guard (and it's LPED=X)
    (@split guard (else { $($diverge:tt)* } = $($tail:tt)*) -> ($pat:tt $guard:tt)) => {
        __guard_impl!(@collect $pat -> (() ()), [$guard $pat ($($tail)*) ({ $($diverge)* })])
    };

    // found a token in the guard
    (@split guard ($head:tt $($tail:tt)*) -> ($pat:tt ($($guard:tt)*))) => {
        __guard_impl!(@split guard ($($tail)*) -> ($pat ($($guard)* $head)))
    };

    // found a token in the pattern
    (@split ($head:tt $($tail:tt)*) -> (($($pat:tt)*) $guard:tt)) => {
        __guard_impl!(@split ($($tail)*) -> (($($pat)* $head) $guard))
    };

    // found an "else DIVERGE" in the expr
    (@split expr (else { $($tail:tt)* }) -> ($pat:tt $guard:tt $expr:tt)) => {
        __guard_impl!(@collect $pat -> (() ()), [$guard $pat $expr ({ $($tail)* })])
    };

    // found an else in the expr with more stuff after it
    (@split expr (else { $($body:tt)* } $($tail:tt)*) -> ($pat:tt $guard:tt ($($expr:tt)*))) => {
        __guard_impl!(@split expr ($($tail)*) -> ($pat $guard ($($expr)* else { $($body)* })))
    };

    // found another token in the expr
    (@split expr ($head:tt $($tail:tt)*) -> ($pat:tt $guard:tt ($($expr:tt)*))) => {
        __guard_impl!(@split expr ($($tail)*) -> ($pat $guard ($($expr)* $head)))
    };

    // 4. entry points
    
    // old syntax
    ({ $($diverge:tt)* } unless $rhs:expr => $($pattern:tt)*) => {
        __guard_impl!(@collect ($($pattern)*) -> (() ()), [(true) ($($pattern)*) ($rhs) ({$($diverge)*})])
        //            |        |                 ||  |    ||      |              |      |
        //            |        |                 ||  |    ||      |              |      ^ diverging expression
        //            |        |                 ||  |    ||      |              ^ expression
        //            |        |                 ||  |    ||      ^ saved copy of pattern
        //            |        |                 ||  |    | ^ pattern guard
        //            |        |                 ||  |    ^ parameters that will be carried through to output stage
        //            |        |                 ||  ^ identifiers bound to mutable captures
        //            |        |                 |^ identifiers bound to immutable captures
        //            |        |                 ^ identifiers found by the scan
        //            |        ^ pattern to be destructively scanned for identifiers
        //            ^ proceed to identifier collection stage

        // FIXME once #14252 is fixed, put "if true" in as the default guard to defeat E0008
    };

    // new syntax
    (let $($tail:tt)*) => {
        __guard_impl!(@split ($($tail)*) -> (() (true)))
        //            |      |               |  |
        //            |      |               |  ^ guard
        //            |      |               ^ pattern
        //            |      ^ tail to be split into "PAT = EXPR else DIVERGE"
        //            ^ first pass will do the parsing
    };
}

/// Match a pattern to an expression, binding identifiers in the calling scope. Diverge if the
/// match fails.
///
/// Supported syntaxes:
///
/// - let `pat` = `rhs` else `diverge`
/// - let `pat` else `diverge` = `rhs`
/// - { `diverge` } unless `rhs` => `pat`
///
/// Inputs:
///
/// - `diverge`: expression which is run if the match fails. Must diverge, or you will get a "match
/// arms have incompatible types" error.
/// - `rhs`: expression to match against the pattern
/// - `pattern`: pattern. Most patterns are allowed, with a few limitations. See the module
/// documentation for details.
#[macro_export]
macro_rules! guard {
    ($($input:tt)*) => {
        __guard_impl!($($input)*)
    };
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

        guard!({ return } unless opt => Stuff::A(Option::Some::<i32>(x), _));           println!("{}", x);
        
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

        guard!({ return } unless dopt => D{});
        guard!({ return } unless Some(Empty) => Some(Empty{}));
    }

    #[cfg(feature = "nightly")]
    #[test]
    fn nightly() {
        // box patterns
        let foo = (box 42, [1, 2, 3]);
        guard!({ return } unless Some(foo) => Some((box x, _)));                           println!("{}", x);

        let mut foo = Some((box 42, [1, 2, 3]));
        {
            guard!({ return } unless foo => Some((box ref x, _)));                         println!("{}", x);
        }
        {
            guard!({ return } unless foo => Some((box ref mut x, _)));                     println!("{}", x);
        }
        {
            guard!({ return } unless foo => Some((box mut x, _)));                         x -= 1; println!("{}", x);
        }

        // slice patterns
        let foo = (box 42, [1, 2, 3]);
        guard!({ return } unless Some(foo) => Some((_, [a, b, c])));                       println!("{} {} {}", a, b, c);
        
        // advanced slice patterns
        let foo = (box 42, [1, 2, 3]);
        guard!({ return } unless Some((foo.0, &foo.1)) => Some((box x, &[head, tail..]))); println!("{} {} {:?}", x, head, tail);
    }

    #[test]
    fn new_syntax() {
        let opt = Some((1, 2));

        // LP=XED
        guard!(let Some((a, b)) = opt else { panic!() });                           println!("{} {}", a, b);
        guard!(let Some((a, b)) = if true  { opt } else { opt } else { panic!() }); println!("{} {}", a, b);
        guard!(let Some((a, b)) = if false { opt } else { opt } else { panic!() }); println!("{} {}", a, b);
        guard!(let Some((a, b)) if b > 0 = opt else { panic!() });                  println!("{} {}", a, b);

        // LPED=X
        guard!(let Some((a, b)) else { panic!() } = opt);                           println!("{} {}", a, b);
        guard!(let Some((a, b)) else { panic!() } = if true  { opt } else { opt }); println!("{} {}", a, b);
        guard!(let Some((a, b)) else { panic!() } = if false { opt } else { opt }); println!("{} {}", a, b);
        guard!(let Some((a, b)) if b > 0 else { panic!() } = opt);                  println!("{} {}", a, b);
    }
}

