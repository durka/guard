extern crate guard;

use guard::guard_unwrap;

#[test]
fn should_be_usable_from_different_crate() {
    guard_unwrap!(let Some(_) = Some(()));
}
