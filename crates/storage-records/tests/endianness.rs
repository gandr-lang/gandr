//! Endianness self-check for the scheduled big-endian lane.
//!
//! The lane sets `GANDR_EXPECT_BIG_ENDIAN` = 1, and only then does the
//! test assert the target is really big-endian; every other run skips.
//! A lane that points at a misconfigured target therefore cannot pass
//! vacuously.

#[test]
fn the_lane_target_is_big_endian_when_declared()
{
    if std::env::var("GANDR_EXPECT_BIG_ENDIAN").as_deref() != Ok("1") {
        return;
    }

    let big_endian = cfg!(target_endian = "big");
    assert!(
        big_endian,
        "the lane declared a big-endian target but the target is not big-endian"
    );
}
