#[inline]
pub const fn mix(mut h: u64) -> u64 {
    h ^= h >> 23;
    h = h.wrapping_mul(0x2127_599b_f432_5c37);
    h ^= h >> 47;
    h
}
