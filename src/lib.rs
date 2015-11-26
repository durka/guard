#![cfg_attr(all(test, feature = "nightly"), feature(braced_empty_structs,
                                                    box_syntax,
                                                    box_patterns,
                                                    slice_patterns,
                                                    advanced_slice_patterns
                                                   ))]

#![cfg_attr(feature = "debug", feature(trace_macros))]
#[cfg(feature = "debug")]
trace_macros!(true);

/// Match a pattern to an expression, binding identifiers in the calling scope. Diverge if the
/// match fails.
#[macro_export]
macro_rules! guard {
    (@as_stmt $s:stmt) => { $s };

    (@collect () -> (($($imms:ident)*) ($($muts:ident)*)), [($($guard:tt)*) ($($pattern:tt)*) ($rhs:expr) ($diverge:expr)]) => {
        // FIXME after #29850 lands, try putting #[allow(unused_mut)] in here somewhere
        guard!(@as_stmt
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
        guard!(@collect ($($inside)* $($tail)*) -> $idents, $thru)
    };
    (@collect ({$($inside:tt)*} $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        guard!(@collect ($($inside)* $($tail)*) -> $idents, $thru)
    };
    (@collect ([$($inside:tt)*] $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        guard!(@collect ($($inside)* $($tail)*) -> $idents, $thru)
    };
    (@collect (, $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        guard!(@collect ($($tail)*) -> $idents, $thru)
    };
    (@collect (.. $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        guard!(@collect ($($tail)*) -> $idents, $thru)
    };
    (@collect (@ $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        guard!(@collect ($($tail)*) -> $idents, $thru)
    };
    (@collect (_ $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        guard!(@collect ($($tail)*) -> $idents, $thru)
    };
    (@collect (& $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        guard!(@collect ($($tail)*) -> $idents, $thru)
    };
    (@collect (:: $pathend:ident $($tail:tt)*) -> $idents:tt, $thru:tt) => { // due to #27832 this has to be before the ident arms instead of near the $pathcomp arm
        guard!(@collect ($($tail)*) -> $idents, $thru)
    };
    (@collect (| $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        guard!(@collect () -> $idents, $thru) // all the bindings on either side of | must be the same, so we don't have to parse the rest
    };
    (@collect (if $($tail:tt)*) -> $idents:tt, [$guard:tt $($rest:tt)*]) => {
        guard!(@collect () -> $idents, [() $($rest)*])
    };
    (@collect ($id:ident: $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        guard!(@collect ($($tail)*) -> $idents, $thru)
    };
    (@collect ($pathcomp:ident :: $pathend:ident $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        guard!(@collect ($($tail)*) -> $idents, $thru)
    };
    (@collect ($id:ident ($($inside:tt)*) $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        guard!(@collect ($($inside)* $($tail)*) -> $idents, $thru)
    };
    (@collect ($id:ident {$($inside:tt)*} $($tail:tt)*) -> $idents:tt, $thru:tt) => {
        guard!(@collect ($($inside)* $($tail)*) -> $idents, $thru)
    };
    (@collect (ref mut $id:ident $($tail:tt)*) -> (($($imms:ident)*) $muts:tt), $thru:tt) => {
        guard!(@collect ($($tail)*) -> (($($imms)* $id) $muts), $thru)
    };
    (@collect (ref $id:ident $($tail:tt)*) -> (($($imms:ident)*) $muts:tt), $thru:tt) => {
        guard!(@collect ($($tail)*) -> (($($imms)* $id) $muts), $thru)
    };
    (@collect (mut $id:ident $($tail:tt)*) -> ($imms:tt ($($muts:ident)*)), $thru:tt) => {
        guard!(@collect ($($tail)*) -> ($imms ($($muts)* $id)), $thru)
    };
    (@collect (box $id:ident $($tail:tt)*) -> (($($imms:ident)*) $muts:tt), $thru:tt) => {
        guard!(@collect ($($tail)*) -> (($($imms)* $id) $muts), $thru)
    };
    (@collect ($id:ident $($tail:tt)*) -> (($($imms:ident)*) $muts:tt), $thru:tt) => {
        guard!(@collect ($($tail)*) -> (($($imms)* $id) $muts), $thru)
    };

    ({ $($diverge:tt)* } unless $rhs:expr => $($pattern:tt)*) => {
        guard!(@collect ($($pattern)*) -> (() ()), [() ($($pattern)*) ($rhs) ({$($diverge)*})])
        // FIXME once #14252 is fixed, put "if true" in as the default guard to defeat E0008
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

