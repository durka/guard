#[macro_use] extern crate guard;
use std::env;

fn main() {
    // read configuration from a certain environment variable
    // do nothing if the variable is missing
    guard!({ return } unless env::var("FOO") => Ok(foo));

    println!("FOO = {}", foo);
}

