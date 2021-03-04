extern crate guard;

use guard::assert_guard;

#[test]
fn should_be_usable_from_different_crate() {
    assert_guard!(let Some(_) = Some(()));
}
