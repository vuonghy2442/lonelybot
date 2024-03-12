// These are bit-mixers, to creater better hash key for the encoded game
fn _murmur64(mut h: u64) -> u64 {
    h ^= h >> 33;
    h *= 0xff51afd7ed558ccd;
    h ^= h >> 33;
    h *= 0xc4ceb9fe1a85ec53;
    h ^= h >> 33;
    h
}

// https://zimbry.blogspot.com/2011/09/better-bit-mixing-improving-on.html
// 	31	0x7fb5d329728ea185	27	0x81dadef4bc2dd44d	33
fn murmur64_mix1(mut h: u64) -> u64 {
    h ^= h >> 31;
    h *= 0x7fb5d329728ea185;
    h ^= h >> 27;
    h *= 0x81dadef4bc2dd44d;
    h ^= h >> 33;
    h
}

fn _fast_hash(mut h: u64) -> u64 {
    h ^= h >> 23;
    h *= 0x2127599bf4325c37;
    h ^= h >> 47;
    h
}

fn _rrmxmx(mut v: u64) -> u64 {
    v ^= v.rotate_right(49) ^ v.rotate_right(24);
    v *= 0x9fb21c651e98df25;
    v ^= v >> 28;
    v *= 0x9fb21c651e98df25;
    v ^ (v >> 28)
}

pub fn default_mixer(h: u64) -> u64 {
    murmur64_mix1(h)
}
