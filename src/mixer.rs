// These are bit-mixers, to creater better hash key for the encoded game
#[inline]
const fn _murmur64(mut h: u64) -> u64 {
    h ^= h >> 33;
    h = h.wrapping_mul(0xff51_afd7_ed55_8ccd);
    h ^= h >> 33;
    h = h.wrapping_mul(0xc4ce_b9fe_1a85_ec53);
    h ^= h >> 33;
    h
}

// https://zimbry.blogspot.com/2011/09/better-bit-mixing-improving-on.html
// 	31	0x7fb5d329728ea185	27	0x81dadef4bc2dd44d	33
#[inline]
const fn murmur64_mix1(mut h: u64) -> u64 {
    h ^= h >> 31;
    h = h.wrapping_mul(0x7fb5_d329_728e_a185);
    h ^= h >> 27;
    h = h.wrapping_mul(0x81da_def4_bc2d_d44d);
    h ^= h >> 33;
    h
}

#[inline]
const fn _fast_hash(mut h: u64) -> u64 {
    h ^= h >> 23;
    h = h.wrapping_mul(0x2127_599b_f432_5c37);
    h ^= h >> 47;
    h
}

#[inline]
const fn _rrmxmx(mut h: u64) -> u64 {
    h ^= h.rotate_right(49) ^ h.rotate_right(24);
    h = h.wrapping_mul(0x9fb2_1c65_1e98_df25);
    h ^= h >> 28;
    h = h.wrapping_mul(0x9fb2_1c65_1e98_df25);
    h ^ (h >> 28)
}

#[inline]
pub const fn mix(h: u64) -> u64 {
    murmur64_mix1(h)
}
