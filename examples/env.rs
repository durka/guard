#![cfg_attr(feature = "nightly", feature(stmt_expr_attributes))]

#[macro_use] extern crate guard;
use std::env;

fn main() {
    // read configuration from a certain environment variable
    // do nothing if the variable is missing
    guard!(let Ok(foo_value) = env::var("FOO") else { return });

    println!("FOO = {}", foo_value);
}

