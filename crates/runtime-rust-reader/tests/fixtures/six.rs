//! Six functions, one for each passage that the record states on the three
//! hosts: six integers, a pair, an aggregate behind an address, two narrow
//! integers, a returned aggregate and an optional reference. Each keeps its
//! symbol in the build.

pub struct Wide
{
    pub a: u64,
    pub b: u64,
    pub c: u64,
}

#[inline(never)]
pub fn weigh(
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
    f: u64,
) -> u64
{
    a ^ b.rotate_left(3)
        ^ c.rotate_left(7)
        ^ d.rotate_left(11)
        ^ e.rotate_left(13)
        ^ f.rotate_left(17)
}

#[inline(never)]
pub fn pair(p: (u32, u64)) -> u64
{
    u64::from(p.0) ^ p.1
}

#[inline(never)]
pub fn wide(w: Wide) -> u64
{
    w.a ^ w.b ^ w.c
}

#[inline(never)]
pub fn narrow(
    x: u8,
    y: i16,
) -> i32
{
    i32::from(x) - i32::from(y)
}

#[inline(never)]
pub fn make(a: u64) -> Wide
{
    Wide {
        a,
        b: a ^ 1,
        c: a ^ 2,
    }
}

#[inline(never)]
pub fn opt(r: Option<&u32>) -> u32
{
    r.copied().unwrap_or(7)
}
