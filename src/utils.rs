#[must_use]
pub const fn min(a: u8, b: u8) -> u8 {
    // finding min value between 2 value
    if a < b {
        a
    } else {
        b
    }
}

#[must_use]
pub const fn full_mask(i: u8) -> u64 {
    // return 2^i - 1 (i bits 1)
    (1 << i) - 1
}

#[inline]
pub const fn mix(mut h: u64) -> u64 {
    // the mix function is the mixer from fasthash64 from here https://github.com/rurban/smhasher/
    h ^= h >> 23;
    h = h.wrapping_mul(0x2127_599b_f432_5c37);
    h ^= h >> 47;
    h
}
