//! The eleven types of `corpus/model/layouts/rust-default.gandr`, each the
//! argument of one function.

pub struct Mixed
{
    pub a: u8,
    pub b: u32,
    pub c: u16,
}

pub struct Wide
{
    pub a: u8,
    pub b: u64,
    pub c: u8,
}

pub struct Small
{
    pub x: u16,
    pub y: u8,
}

pub struct Flagged
{
    pub a: u8,
    pub b: bool,
    pub c: u16,
}

pub struct Signed
{
    pub a: i32,
    pub b: i64,
    pub c: u8,
}

pub enum MaybeRef<'a>
{
    Some(&'a u32),
    None,
}

pub enum MaybeFlag
{
    Set(bool),
    Unset,
}

pub enum Either
{
    Left(u32),
    Right(u16),
}

pub enum Jagged
{
    Full(u32, bool),
    Thin(u8),
}

pub enum ThreeRef<'a>
{
    First,
    Held(&'a u32),
    Last,
}

pub enum ThreeFlag
{
    First,
    Held(bool),
    Last,
}

#[inline(never)]
pub fn mixed(_: Mixed)
{
}

#[inline(never)]
pub fn wide(_: Wide)
{
}

#[inline(never)]
pub fn small(_: Small)
{
}

#[inline(never)]
pub fn flagged(_: Flagged)
{
}

#[inline(never)]
pub fn signed(_: Signed)
{
}

#[inline(never)]
pub fn maybe_ref(_: MaybeRef<'_>)
{
}

#[inline(never)]
pub fn maybe_flag(_: MaybeFlag)
{
}

#[inline(never)]
pub fn either(_: Either)
{
}

#[inline(never)]
pub fn jagged(_: Jagged)
{
}

#[inline(never)]
pub fn three_ref(_: ThreeRef<'_>)
{
}

#[inline(never)]
pub fn three_flag(_: ThreeFlag)
{
}
