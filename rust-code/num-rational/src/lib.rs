// Copyright 2013-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Rational numbers
//!
//! ## Compatibility
//!
//! The `num-rational` crate is tested for rustc 1.60 and greater.

#![recursion_limit = "1024"]
#![doc(html_root_url = "https://docs.rs/num-rational/0.4")]
#![no_std]
// Rational32 ops often use other "suspicious" ops
#![allow(clippy::suspicious_arithmetic_impl)]
#![allow(clippy::suspicious_op_assign_impl)]

#[cfg(feature = "std")]
#[macro_use]
extern crate std;

use core::cmp;
use core::fmt;
use core::fmt::{Binary, Display, Formatter, LowerExp, LowerHex, Octal, UpperExp, UpperHex};
use core::hash::{Hash, Hasher};
use core::ops::{Add, Div, Mul, Neg, Rem, ShlAssign, Sub};
use core::str::FromStr;
#[cfg(feature = "std")]
use std::error::Error;

use num_integer::Integer;
use num_traits::float::FloatCore;
use num_traits::{
    Bounded, CheckedAdd, CheckedDiv, CheckedMul, CheckedSub, ConstOne, ConstZero, FromPrimitive,
    Inv, Num, NumCast, One, Pow, Signed, ToPrimitive, Unsigned, Zero,
};
use wasm_bindgen::prelude::*;

type T = i32;

mod pow;

/// Represents the ratio between two numbers.
#[derive(Copy, Clone, Debug)]
#[wasm_bindgen]
#[allow(missing_docs)]
pub struct Rational32 {
    /// Numerator.
    numer: i32,
    /// Denominator.
    denom: i32,
}

/// These method are `const`.
impl Rational32 {
    /// Creates a `Rational32` without checking for `denom == 0` or reducing.
    ///
    /// **There are several methods that will panic if used on a `Rational32` with
    /// `denom == 0`.**
    #[inline]
    pub const fn new_raw(numer: T, denom: T) -> Rational32 {
        Rational32 { numer, denom }
    }

    /// Deconstructs a `Rational32` into its numerator and denominator.
    #[inline]
    pub fn into_raw(self) -> (i32, i32) {
        (self.numer, self.denom)
    }

    /// Gets an immutable reference to the numerator.
    #[inline]
    pub const fn numer(&self) -> &T {
        &self.numer
    }

    /// Gets an immutable reference to the denominator.
    #[inline]
    pub const fn denom(&self) -> &T {
        &self.denom
    }
}

impl Rational32 {
    /// Creates a new `Rational32`.
    ///
    /// **Panics if `denom` is zero.**
    #[inline]
    pub fn new(numer: T, denom: T) -> Rational32 {
        let mut ret = Rational32::new_raw(numer, denom);
        ret.reduce();
        ret
    }

    /// Creates a `Rational32` representing the integer `t`.
    #[inline]
    pub fn from_integer(t: T) -> Rational32 {
        Rational32::new_raw(t, One::one())
    }

    /// Converts to an integer, rounding towards zero.
    #[inline]
    pub fn to_integer(&self) -> T {
        self.trunc().numer
    }

    /// Returns true if the rational number is an integer (denominator is 1).
    #[inline]
    pub fn is_integer(&self) -> bool {
        self.denom.is_one()
    }

    /// Puts self into lowest terms, with `denom` > 0.
    ///
    /// **Panics if `denom` is zero.**
    fn reduce(&mut self) {
        if self.denom.is_zero() {
            panic!("denominator == 0");
        }
        if self.numer.is_zero() {
            self.denom.set_one();
            return;
        }
        if self.numer == self.denom {
            self.set_one();
            return;
        }
        let g: T = self.numer.gcd(&self.denom);

        // FIXME(#5992): assignment operator overloads
        // T: Clone + Integer != T: Clone + NumAssign

        #[inline]
        fn replace_with(x: &mut T, f: impl FnOnce(T) -> T) {
            let y = core::mem::replace(x, T::zero());
            *x = f(y);
        }

        // self.numer /= g;
        replace_with(&mut self.numer, |x| x / g.clone());

        // self.denom /= g;
        replace_with(&mut self.denom, |x| x / g);

        // keep denom positive!
        if self.denom < T::zero() {
            replace_with(&mut self.numer, |x| T::zero() - x);
            replace_with(&mut self.denom, |x| T::zero() - x);
        }
    }

    /// Returns a reduced copy of self.
    ///
    /// In general, it is not necessary to use this method, as the only
    /// method of procuring a non-reduced fraction is through `new_raw`.
    ///
    /// **Panics if `denom` is zero.**
    pub fn reduced(&self) -> Rational32 {
        let mut ret = self.clone();
        ret.reduce();
        ret
    }

    /// Returns the reciprocal.
    ///
    /// **Panics if the `Rational32` is zero.**
    #[inline]
    pub fn recip(&self) -> Rational32 {
        self.clone().into_recip()
    }

    #[inline]
    fn into_recip(self) -> Rational32 {
        match self.numer.cmp(&T::zero()) {
            cmp::Ordering::Equal => panic!("division by zero"),
            cmp::Ordering::Greater => Rational32::new_raw(self.denom, self.numer),
            cmp::Ordering::Less => {
                Rational32::new_raw(T::zero() - self.denom, T::zero() - self.numer)
            }
        }
    }

    /// Rounds towards minus infinity.
    #[inline]
    pub fn floor(&self) -> Rational32 {
        if *self < Zero::zero() {
            let one: T = One::one();
            Rational32::from_integer(
                (self.numer.clone() - self.denom.clone() + one) / self.denom.clone(),
            )
        } else {
            Rational32::from_integer(self.numer.clone() / self.denom.clone())
        }
    }

    /// Rounds towards plus infinity.
    #[inline]
    pub fn ceil(&self) -> Rational32 {
        if *self < Zero::zero() {
            Rational32::from_integer(self.numer.clone() / self.denom.clone())
        } else {
            let one: T = One::one();
            Rational32::from_integer(
                (self.numer.clone() + self.denom.clone() - one) / self.denom.clone(),
            )
        }
    }

    /// Rounds to the nearest integer. Rounds half-way cases away from zero.
    #[inline]
    pub fn round(&self) -> Rational32 {
        let zero: Rational32 = Zero::zero();
        let one: T = One::one();
        let two: T = one.clone() + one.clone();

        // Find unsigned fractional part of rational number
        let mut fractional = self.fract();
        if fractional < zero {
            fractional = zero - fractional
        };

        // The algorithm compares the unsigned fractional part with 1/2, that
        // is, a/b >= 1/2, or a >= b/2. For odd denominators, we use
        // a >= (b/2)+1. This avoids overflow issues.
        let half_or_larger = if fractional.denom.is_even() {
            fractional.numer >= fractional.denom / two
        } else {
            fractional.numer >= (fractional.denom / two) + one
        };

        if half_or_larger {
            let one: Rational32 = One::one();
            if *self >= Zero::zero() {
                self.trunc() + one
            } else {
                self.trunc() - one
            }
        } else {
            self.trunc()
        }
    }

    /// Rounds towards zero.
    #[inline]
    pub fn trunc(&self) -> Rational32 {
        Rational32::from_integer(self.numer.clone() / self.denom.clone())
    }

    /// Returns the fractional part of a number, with division rounded towards zero.
    ///
    /// Satisfies `self == self.trunc() + self.fract()`.
    #[inline]
    pub fn fract(&self) -> Rational32 {
        Rational32::new_raw(self.numer.clone() % self.denom.clone(), self.denom.clone())
    }

    /// Raises the `Rational32` to the power of an exponent.
    #[inline]
    pub fn pow(&self, expon: i32) -> Rational32
    where
        for<'a> &'a T: Pow<u32, Output = T>,
    {
        Pow::pow(self, expon)
    }
}

impl Default for Rational32 {
    /// Returns zero
    fn default() -> Self {
        Rational32::zero()
    }
}

// From integer
impl From<T> for Rational32
where
    T: Clone + Integer,
{
    fn from(x: T) -> Rational32 {
        Rational32::from_integer(x)
    }
}

// From pair (through the `new` constructor)
impl From<(T, T)> for Rational32
where
    T: Clone + Integer,
{
    fn from(pair: (T, T)) -> Rational32 {
        Rational32::new(pair.0, pair.1)
    }
}

// Comparisons

// Mathematically, comparing a/b and c/d is the same as comparing a*d and b*c, but it's very easy
// for those multiplications to overflow fixed-size integers, so we need to take care.

impl Ord for Rational32 {
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        // With equal denominators, the numerators can be directly compared
        if self.denom == other.denom {
            let ord = self.numer.cmp(&other.numer);
            return if self.denom < T::zero() {
                ord.reverse()
            } else {
                ord
            };
        }

        // With equal numerators, the denominators can be inversely compared
        if self.numer == other.numer {
            if self.numer.is_zero() {
                return cmp::Ordering::Equal;
            }
            let ord = self.denom.cmp(&other.denom);
            return if self.numer < T::zero() {
                ord
            } else {
                ord.reverse()
            };
        }

        // Unfortunately, we don't have CheckedMul to try.  That could sometimes avoid all the
        // division below, or even always avoid it for BigInt and BigUint.
        // FIXME- future breaking change to add Checked* to Integer?

        // Compare as floored integers and remainders
        let (self_int, self_rem) = self.numer.div_mod_floor(&self.denom);
        let (other_int, other_rem) = other.numer.div_mod_floor(&other.denom);
        match self_int.cmp(&other_int) {
            cmp::Ordering::Greater => cmp::Ordering::Greater,
            cmp::Ordering::Less => cmp::Ordering::Less,
            cmp::Ordering::Equal => {
                match (self_rem.is_zero(), other_rem.is_zero()) {
                    (true, true) => cmp::Ordering::Equal,
                    (true, false) => cmp::Ordering::Less,
                    (false, true) => cmp::Ordering::Greater,
                    (false, false) => {
                        // Compare the reciprocals of the remaining fractions in reverse
                        let self_recip = Rational32::new_raw(self.denom.clone(), self_rem);
                        let other_recip = Rational32::new_raw(other.denom.clone(), other_rem);
                        self_recip.cmp(&other_recip).reverse()
                    }
                }
            }
        }
    }
}

impl PartialOrd for Rational32 {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Rational32 {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == cmp::Ordering::Equal
    }
}

impl Eq for Rational32 {}

// NB: We can't just `#[derive(Hash)]`, because it needs to agree
// with `Eq` even for non-reduced ratios.
impl Hash for Rational32 {
    fn hash<H: Hasher>(&self, state: &mut H) {
        recurse(&self.numer, &self.denom, state);

        fn recurse<H: Hasher>(numer: &T, denom: &T, state: &mut H) {
            if !denom.is_zero() {
                let (int, rem) = numer.div_mod_floor(denom);
                int.hash(state);
                recurse(denom, &rem, state);
            } else {
                denom.hash(state);
            }
        }
    }
}

mod iter_sum_product {
    use crate::Rational32;
    use core::iter::{Product, Sum};
    use num_integer::Integer;
    use num_traits::{One, Zero};

    impl Sum for Rational32 {
        fn sum<I>(iter: I) -> Self
        where
            I: Iterator<Item = Rational32>,
        {
            iter.fold(Self::zero(), |sum, num| sum + num)
        }
    }

    impl<'a> Sum<&'a Rational32> for Rational32 {
        fn sum<I>(iter: I) -> Self
        where
            I: Iterator<Item = &'a Rational32>,
        {
            iter.fold(Self::zero(), |sum, num| sum + num)
        }
    }

    impl Product for Rational32 {
        fn product<I>(iter: I) -> Self
        where
            I: Iterator<Item = Rational32>,
        {
            iter.fold(Self::one(), |prod, num| prod * num)
        }
    }

    impl<'a> Product<&'a Rational32> for Rational32 {
        fn product<I>(iter: I) -> Self
        where
            I: Iterator<Item = &'a Rational32>,
        {
            iter.fold(Self::one(), |prod, num| prod * num)
        }
    }
}

mod opassign {
    use core::ops::{AddAssign, DivAssign, MulAssign, RemAssign, SubAssign};

    use crate::Rational32;
    use num_integer::Integer;
    use num_traits::NumAssign;

    impl AddAssign for Rational32 {
        fn add_assign(&mut self, other: Rational32) {
            if self.denom == other.denom {
                self.numer += other.numer
            } else {
                let lcm = self.denom.lcm(&other.denom);
                let lhs_numer = self.numer.clone() * (lcm.clone() / self.denom.clone());
                let rhs_numer = other.numer * (lcm.clone() / other.denom);
                self.numer = lhs_numer + rhs_numer;
                self.denom = lcm;
            }
            self.reduce();
        }
    }

    // (a/b) / (c/d) = (a/gcd_ac)*(d/gcd_bd) / ((c/gcd_ac)*(b/gcd_bd))
    impl DivAssign for Rational32 {
        fn div_assign(&mut self, other: Rational32) {
            let gcd_ac = self.numer.gcd(&other.numer);
            let gcd_bd = self.denom.gcd(&other.denom);
            self.numer /= gcd_ac.clone();
            self.numer *= other.denom / gcd_bd.clone();
            self.denom /= gcd_bd;
            self.denom *= other.numer / gcd_ac;
            self.reduce(); // TODO: remove this line. see #8.
        }
    }

    // a/b * c/d = (a/gcd_ad)*(c/gcd_bc) / ((d/gcd_ad)*(b/gcd_bc))
    impl MulAssign for Rational32 {
        fn mul_assign(&mut self, other: Rational32) {
            let gcd_ad = self.numer.gcd(&other.denom);
            let gcd_bc = self.denom.gcd(&other.numer);
            self.numer /= gcd_ad.clone();
            self.numer *= other.numer / gcd_bc.clone();
            self.denom /= gcd_bc;
            self.denom *= other.denom / gcd_ad;
            self.reduce(); // TODO: remove this line. see #8.
        }
    }

    impl RemAssign for Rational32 {
        fn rem_assign(&mut self, other: Rational32) {
            if self.denom == other.denom {
                self.numer %= other.numer
            } else {
                let lcm = self.denom.lcm(&other.denom);
                let lhs_numer = self.numer.clone() * (lcm.clone() / self.denom.clone());
                let rhs_numer = other.numer * (lcm.clone() / other.denom);
                self.numer = lhs_numer % rhs_numer;
                self.denom = lcm;
            }
            self.reduce();
        }
    }

    impl SubAssign for Rational32 {
        fn sub_assign(&mut self, other: Rational32) {
            if self.denom == other.denom {
                self.numer -= other.numer
            } else {
                let lcm = self.denom.lcm(&other.denom);
                let lhs_numer = self.numer.clone() * (lcm.clone() / self.denom.clone());
                let rhs_numer = other.numer * (lcm.clone() / other.denom);
                self.numer = lhs_numer - rhs_numer;
                self.denom = lcm;
            }
            self.reduce();
        }
    }

    type T = i32;

    // a/b + c/1 = (a*1 + b*c) / (b*1) = (a + b*c) / b
    impl AddAssign<i32> for Rational32 {
        fn add_assign(&mut self, other: T) {
            self.numer += self.denom.clone() * other;
            self.reduce();
        }
    }

    impl DivAssign<T> for Rational32 {
        fn div_assign(&mut self, other: T) {
            let gcd = self.numer.gcd(&other);
            self.numer /= gcd.clone();
            self.denom *= other / gcd;
            self.reduce(); // TODO: remove this line. see #8.
        }
    }

    impl MulAssign<T> for Rational32 {
        fn mul_assign(&mut self, other: T) {
            let gcd = self.denom.gcd(&other);
            self.denom /= gcd.clone();
            self.numer *= other / gcd;
            self.reduce(); // TODO: remove this line. see #8.
        }
    }

    // a/b % c/1 = (a*1 % b*c) / (b*1) = (a % b*c) / b
    impl RemAssign<T> for Rational32 {
        fn rem_assign(&mut self, other: T) {
            self.numer %= self.denom.clone() * other;
            self.reduce();
        }
    }

    // a/b - c/1 = (a*1 - b*c) / (b*1) = (a - b*c) / b
    impl SubAssign<T> for Rational32 {
        fn sub_assign(&mut self, other: T) {
            self.numer -= self.denom.clone() * other;
            self.reduce();
        }
    }

    macro_rules! forward_op_assign {
        (impl $imp:ident, $method:ident) => {
            impl<'a> $imp<&'a Rational32> for Rational32 {
                #[inline]
                fn $method(&mut self, other: &Rational32) {
                    self.$method(other.clone())
                }
            }
            impl<'a> $imp<&'a i32> for Rational32 {
                #[inline]
                fn $method(&mut self, other: &T) {
                    self.$method(other.clone())
                }
            }
        };
    }

    forward_op_assign!(impl AddAssign, add_assign);
    forward_op_assign!(impl DivAssign, div_assign);
    forward_op_assign!(impl MulAssign, mul_assign);
    forward_op_assign!(impl RemAssign, rem_assign);
    forward_op_assign!(impl SubAssign, sub_assign);
}

macro_rules! forward_ref_ref_binop {
    (impl $imp:ident, $method:ident) => {
        impl<'a, 'b> $imp<&'b Rational32> for &'a Rational32 {
            type Output = Rational32;

            #[inline]
            fn $method(self, other: &'b Rational32) -> Rational32 {
                self.clone().$method(other.clone())
            }
        }
        impl<'a, 'b> $imp<&'b T> for &'a Rational32 {
            type Output = Rational32;

            #[inline]
            fn $method(self, other: &'b T) -> Rational32 {
                self.clone().$method(other.clone())
            }
        }
    };
}

macro_rules! forward_ref_val_binop {
    (impl $imp:ident, $method:ident) => {
        impl<'a> $imp<Rational32> for &'a Rational32 {
            type Output = Rational32;

            #[inline]
            fn $method(self, other: Rational32) -> Rational32 {
                self.clone().$method(other)
            }
        }
        impl<'a> $imp<T> for &'a Rational32 {
            type Output = Rational32;

            #[inline]
            fn $method(self, other: T) -> Rational32 {
                self.clone().$method(other)
            }
        }
    };
}

macro_rules! forward_val_ref_binop {
    (impl $imp:ident, $method:ident) => {
        impl<'a> $imp<&'a Rational32> for Rational32 {
            type Output = Rational32;

            #[inline]
            fn $method(self, other: &Rational32) -> Rational32 {
                self.$method(other.clone())
            }
        }
        impl<'a> $imp<&'a T> for Rational32 {
            type Output = Rational32;

            #[inline]
            fn $method(self, other: &T) -> Rational32 {
                self.$method(other.clone())
            }
        }
    };
}

macro_rules! forward_all_binop {
    (impl $imp:ident, $method:ident) => {
        forward_ref_ref_binop!(impl $imp, $method);
        forward_ref_val_binop!(impl $imp, $method);
        forward_val_ref_binop!(impl $imp, $method);
    };
}

// Arithmetic
forward_all_binop!(impl Mul, mul);
// a/b * c/d = (a/gcd_ad)*(c/gcd_bc) / ((d/gcd_ad)*(b/gcd_bc))
impl Mul<Rational32> for Rational32
where
    T: Clone + Integer,
{
    type Output = Rational32;
    #[inline]
    fn mul(self, rhs: Rational32) -> Rational32 {
        let gcd_ad = self.numer.gcd(&rhs.denom);
        let gcd_bc = self.denom.gcd(&rhs.numer);
        Rational32::new(
            self.numer / gcd_ad.clone() * (rhs.numer / gcd_bc.clone()),
            self.denom / gcd_bc * (rhs.denom / gcd_ad),
        )
    }
}
// a/b * c/1 = (a*c) / (b*1) = (a*c) / b
impl Mul<T> for Rational32 {
    type Output = Rational32;
    #[inline]
    fn mul(self, rhs: T) -> Rational32 {
        let gcd = self.denom.gcd(&rhs);
        Rational32::new(self.numer * (rhs / gcd.clone()), self.denom / gcd)
    }
}

forward_all_binop!(impl Div, div);
// (a/b) / (c/d) = (a/gcd_ac)*(d/gcd_bd) / ((c/gcd_ac)*(b/gcd_bd))
impl Div<Rational32> for Rational32
where
    T: Clone + Integer,
{
    type Output = Rational32;

    #[inline]
    fn div(self, rhs: Rational32) -> Rational32 {
        let gcd_ac = self.numer.gcd(&rhs.numer);
        let gcd_bd = self.denom.gcd(&rhs.denom);
        Rational32::new(
            self.numer / gcd_ac.clone() * (rhs.denom / gcd_bd.clone()),
            self.denom / gcd_bd * (rhs.numer / gcd_ac),
        )
    }
}
// (a/b) / (c/1) = (a*1) / (b*c) = a / (b*c)
impl Div<T> for Rational32
where
    T: Clone + Integer,
{
    type Output = Rational32;

    #[inline]
    fn div(self, rhs: T) -> Rational32 {
        let gcd = self.numer.gcd(&rhs);
        Rational32::new(self.numer / gcd.clone(), self.denom * (rhs / gcd))
    }
}

macro_rules! arith_impl {
    (impl $imp:ident, $method:ident) => {
        forward_all_binop!(impl $imp, $method);
        // Abstracts a/b `op` c/d = (a*lcm/b `op` c*lcm/d)/lcm where lcm = lcm(b,d)
        impl $imp<Rational32> for Rational32 {
            type Output = Rational32;
            #[inline]
            fn $method(self, rhs: Rational32) -> Rational32 {
                if self.denom == rhs.denom {
                    return Rational32::new(self.numer.$method(rhs.numer), rhs.denom);
                }
                let lcm = self.denom.lcm(&rhs.denom);
                let lhs_numer = self.numer * (lcm.clone() / self.denom);
                let rhs_numer = rhs.numer * (lcm.clone() / rhs.denom);
                Rational32::new(lhs_numer.$method(rhs_numer), lcm)
            }
        }
        // Abstracts the a/b `op` c/1 = (a*1 `op` b*c) / (b*1) = (a `op` b*c) / b pattern
        impl $imp<T> for Rational32 {
            type Output = Rational32;
            #[inline]
            fn $method(self, rhs: T) -> Rational32 {
                Rational32::new(self.numer.$method(self.denom.clone() * rhs), self.denom)
            }
        }
    };
}

arith_impl!(impl Add, add);
arith_impl!(impl Sub, sub);
arith_impl!(impl Rem, rem);

// a/b * c/d = (a*c)/(b*d)
impl CheckedMul for Rational32
where
    T: Clone + Integer + CheckedMul,
{
    #[inline]
    fn checked_mul(&self, rhs: &Rational32) -> Option<Rational32> {
        let gcd_ad = self.numer.gcd(&rhs.denom);
        let gcd_bc = self.denom.gcd(&rhs.numer);
        Some(Rational32::new(
            (self.numer.clone() / gcd_ad.clone())
                .checked_mul(rhs.numer.clone() / gcd_bc.clone())?,
            (self.denom.clone() / gcd_bc).checked_mul(rhs.denom.clone() / gcd_ad)?,
        ))
    }
}

// (a/b) / (c/d) = (a*d)/(b*c)
impl CheckedDiv for Rational32
where
    T: Clone + Integer + CheckedMul,
{
    #[inline]
    fn checked_div(&self, rhs: &Rational32) -> Option<Rational32> {
        if rhs.is_zero() {
            return None;
        }
        let (numer, denom) = if self.denom == rhs.denom {
            (self.numer.clone(), rhs.numer.clone())
        } else if self.numer == rhs.numer {
            (rhs.denom.clone(), self.denom.clone())
        } else {
            let gcd_ac = self.numer.gcd(&rhs.numer);
            let gcd_bd = self.denom.gcd(&rhs.denom);
            (
                (self.numer.clone() / gcd_ac.clone())
                    .checked_mul(rhs.denom.clone() / gcd_bd.clone())?,
                (self.denom.clone() / gcd_bd).checked_mul(rhs.numer.clone() / gcd_ac)?,
            )
        };
        // Manual `reduce()`, avoiding sharp edges
        if denom.is_zero() {
            None
        } else if numer.is_zero() {
            Some(Self::zero())
        } else if numer == denom {
            Some(Self::one())
        } else {
            let g = numer.gcd(&denom);
            let numer = numer / g.clone();
            let denom = denom / g;
            let raw = if denom < T::zero() {
                // We need to keep denom positive, but 2's-complement MIN may
                // overflow negation -- instead we can check multiplying -1.
                let n1 = T::zero() - T::one();
                Rational32::new_raw(numer.checked_mul(n1)?, denom.checked_mul(n1)?)
            } else {
                Rational32::new_raw(numer, denom)
            };
            Some(raw)
        }
    }
}

// As arith_impl! but for Checked{Add,Sub} traits
macro_rules! checked_arith_impl {
    (impl $imp:ident, $method:ident) => {
        impl $imp for Rational32 {
            #[inline]
            fn $method(&self, rhs: &Rational32) -> Option<Rational32> {
                let gcd = self.denom.clone().gcd(&rhs.denom);
                let lcm = (self.denom.clone() / gcd.clone()).checked_mul(rhs.denom)?;
                let lhs_numer = (lcm.clone() / self.denom.clone()).checked_mul(self.numer)?;
                let rhs_numer = (lcm.clone() / rhs.denom.clone()).checked_mul(rhs.numer)?;
                Some(Rational32::new(lhs_numer.$method(rhs_numer)?, lcm))
            }
        }
    };
}

// a/b + c/d = (lcm/b*a + lcm/d*c)/lcm, where lcm = lcm(b,d)
checked_arith_impl!(impl CheckedAdd, checked_add);

// a/b - c/d = (lcm/b*a - lcm/d*c)/lcm, where lcm = lcm(b,d)
checked_arith_impl!(impl CheckedSub, checked_sub);

impl Neg for Rational32
where
    T: Clone + Integer + Neg<Output = T>,
{
    type Output = Rational32;

    #[inline]
    fn neg(self) -> Rational32 {
        Rational32::new_raw(-self.numer, self.denom)
    }
}

impl<'a> Neg for &'a Rational32 {
    type Output = Rational32;

    #[inline]
    fn neg(self) -> Rational32 {
        -self.clone()
    }
}

impl Inv for Rational32
where
    T: Clone + Integer,
{
    type Output = Rational32;

    #[inline]
    fn inv(self) -> Rational32 {
        self.recip()
    }
}

impl<'a> Inv for &'a Rational32
where
    T: Clone + Integer,
{
    type Output = Rational32;

    #[inline]
    fn inv(self) -> Rational32 {
        self.recip()
    }
}

// Constants
impl Rational32 {
    /// A constant `Rational32` 0/1.
    pub const ZERO: Self = Self::new_raw(T::ZERO, T::ONE);
}

impl ConstZero for Rational32 {
    const ZERO: Self = Self::ZERO;
}

impl Zero for Rational32 {
    #[inline]
    fn zero() -> Rational32 {
        Rational32::new_raw(Zero::zero(), One::one())
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.numer.is_zero()
    }

    #[inline]
    fn set_zero(&mut self) {
        self.numer.set_zero();
        self.denom.set_one();
    }
}

impl Rational32 {
    /// A constant `Rational32` 1/1.
    pub const ONE: Self = Self::new_raw(T::ONE, T::ONE);
}

impl ConstOne for Rational32 {
    const ONE: Self = Self::ONE;
}

impl One for Rational32 {
    #[inline]
    fn one() -> Rational32 {
        Rational32::new_raw(One::one(), One::one())
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.numer == self.denom
    }

    #[inline]
    fn set_one(&mut self) {
        self.numer.set_one();
        self.denom.set_one();
    }
}

impl Num for Rational32 {
    type FromStrRadixErr = ParseRatioError;

    /// Parses `numer/denom` where the numbers are in base `radix`.
    fn from_str_radix(s: &str, radix: u32) -> Result<Rational32, ParseRatioError> {
        if s.splitn(2, '/').count() == 2 {
            let mut parts = s.splitn(2, '/').map(|ss| {
                T::from_str_radix(ss, radix).map_err(|_| ParseRatioError {
                    kind: RatioErrorKind::ParseError,
                })
            });
            let numer: T = parts.next().unwrap()?;
            let denom: T = parts.next().unwrap()?;
            if denom.is_zero() {
                Err(ParseRatioError {
                    kind: RatioErrorKind::ZeroDenominator,
                })
            } else {
                Ok(Rational32::new(numer, denom))
            }
        } else {
            Err(ParseRatioError {
                kind: RatioErrorKind::ParseError,
            })
        }
    }
}

impl Signed for Rational32 {
    #[inline]
    fn abs(&self) -> Rational32 {
        if self.is_negative() {
            -self.clone()
        } else {
            self.clone()
        }
    }

    #[inline]
    fn abs_sub(&self, other: &Rational32) -> Rational32 {
        if *self <= *other {
            Zero::zero()
        } else {
            self - other
        }
    }

    #[inline]
    fn signum(&self) -> Rational32 {
        if self.is_positive() {
            Self::one()
        } else if self.is_zero() {
            Self::zero()
        } else {
            -Self::one()
        }
    }

    #[inline]
    fn is_positive(&self) -> bool {
        (self.numer.is_positive() && self.denom.is_positive())
            || (self.numer.is_negative() && self.denom.is_negative())
    }

    #[inline]
    fn is_negative(&self) -> bool {
        (self.numer.is_negative() && self.denom.is_positive())
            || (self.numer.is_positive() && self.denom.is_negative())
    }
}

// String conversions
macro_rules! impl_formatting {
    ($fmt_trait:ident, $prefix:expr, $fmt_str:expr, $fmt_alt:expr) => {
        impl $fmt_trait for Rational32 {
            #[cfg(feature = "std")]
            fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
                let pre_pad = if self.denom.is_one() {
                    format!($fmt_str, self.numer)
                } else {
                    if f.alternate() {
                        format!(concat!($fmt_str, "/", $fmt_alt), self.numer, self.denom)
                    } else {
                        format!(concat!($fmt_str, "/", $fmt_str), self.numer, self.denom)
                    }
                };
                if let Some(pre_pad) = pre_pad.strip_prefix("-") {
                    f.pad_integral(false, $prefix, pre_pad)
                } else {
                    f.pad_integral(true, $prefix, &pre_pad)
                }
            }
            #[cfg(not(feature = "std"))]
            fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
                let plus = if f.sign_plus() && self.numer >= T::zero() {
                    "+"
                } else {
                    ""
                };
                if self.denom.is_one() {
                    if f.alternate() {
                        write!(f, concat!("{}", $fmt_alt), plus, self.numer)
                    } else {
                        write!(f, concat!("{}", $fmt_str), plus, self.numer)
                    }
                } else {
                    if f.alternate() {
                        write!(
                            f,
                            concat!("{}", $fmt_alt, "/", $fmt_alt),
                            plus, self.numer, self.denom
                        )
                    } else {
                        write!(
                            f,
                            concat!("{}", $fmt_str, "/", $fmt_str),
                            plus, self.numer, self.denom
                        )
                    }
                }
            }
        }
    };
}

impl_formatting!(Display, "", "{}", "{:#}");
impl_formatting!(Octal, "0o", "{:o}", "{:#o}");
impl_formatting!(Binary, "0b", "{:b}", "{:#b}");
impl_formatting!(LowerHex, "0x", "{:x}", "{:#x}");
impl_formatting!(UpperHex, "0x", "{:X}", "{:#X}");
impl_formatting!(LowerExp, "", "{:e}", "{:#e}");
impl_formatting!(UpperExp, "", "{:E}", "{:#E}");

impl FromStr for Rational32 {
    type Err = ParseRatioError;

    /// Parses `numer/denom` or just `numer`.
    fn from_str(s: &str) -> Result<Rational32, ParseRatioError> {
        let mut split = s.splitn(2, '/');

        let n = split.next().ok_or(ParseRatioError {
            kind: RatioErrorKind::ParseError,
        })?;
        let num = FromStr::from_str(n).map_err(|_| ParseRatioError {
            kind: RatioErrorKind::ParseError,
        })?;

        let d = split.next().unwrap_or("1");
        let den = FromStr::from_str(d).map_err(|_| ParseRatioError {
            kind: RatioErrorKind::ParseError,
        })?;

        if Zero::is_zero(&den) {
            Err(ParseRatioError {
                kind: RatioErrorKind::ZeroDenominator,
            })
        } else {
            Ok(Rational32::new(num, den))
        }
    }
}

impl From<Rational32> for (T, T) {
    fn from(val: Rational32) -> Self {
        (val.numer, val.denom)
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for Rational32
where
    T: serde::Serialize + Clone + Integer + PartialOrd,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        (self.numer(), self.denom()).serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, T> serde::Deserialize<'de> for Rational32
where
    T: serde::Deserialize<'de> + Clone + Integer + PartialOrd,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        use serde::de::Error;
        use serde::de::Unexpected;
        let (numer, denom): (T, T) = serde::Deserialize::deserialize(deserializer)?;
        if denom.is_zero() {
            Err(Error::invalid_value(
                Unexpected::Signed(0),
                &"a ratio with non-zero denominator",
            ))
        } else {
            Ok(Rational32::new_raw(numer, denom))
        }
    }
}

// FIXME: Bubble up specific errors
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct ParseRatioError {
    kind: RatioErrorKind,
}

#[derive(Copy, Clone, Debug, PartialEq)]
enum RatioErrorKind {
    ParseError,
    ZeroDenominator,
}

impl fmt::Display for ParseRatioError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.description().fmt(f)
    }
}

#[cfg(feature = "std")]
impl Error for ParseRatioError {
    #[allow(deprecated)]
    fn description(&self) -> &str {
        self.kind.description()
    }
}

impl RatioErrorKind {
    fn description(&self) -> &'static str {
        match *self {
            RatioErrorKind::ParseError => "failed to parse integer",
            RatioErrorKind::ZeroDenominator => "zero value denominator",
        }
    }
}

macro_rules! from_primitive_integer {
    ($typ:ty, $approx:ident) => {
        impl FromPrimitive for Rational32 {
            fn from_i64(n: i64) -> Option<Self> {
                <$typ as FromPrimitive>::from_i64(n).map(Rational32::from_integer)
            }

            fn from_i128(n: i128) -> Option<Self> {
                <$typ as FromPrimitive>::from_i128(n).map(Rational32::from_integer)
            }

            fn from_u64(n: u64) -> Option<Self> {
                <$typ as FromPrimitive>::from_u64(n).map(Rational32::from_integer)
            }

            fn from_u128(n: u128) -> Option<Self> {
                <$typ as FromPrimitive>::from_u128(n).map(Rational32::from_integer)
            }

            fn from_f32(n: f32) -> Option<Self> {
                $approx(n, 10e-20, 30)
            }

            fn from_f64(n: f64) -> Option<Self> {
                $approx(n, 10e-20, 30)
            }
        }
    };
}

// from_primitive_integer!(i8, approximate_float);
// from_primitive_integer!(i16, approximate_float);
// from_primitive_integer!(i32, approximate_float);
// from_primitive_integer!(i64, approximate_float);
// from_primitive_integer!(i128, approximate_float);
// from_primitive_integer!(isize, approximate_float);

// from_primitive_integer!(u8, approximate_float_unsigned);
// from_primitive_integer!(u16, approximate_float_unsigned);
// from_primitive_integer!(u32, approximate_float_unsigned);
// from_primitive_integer!(u64, approximate_float_unsigned);
// from_primitive_integer!(u128, approximate_float_unsigned);
// from_primitive_integer!(usize, approximate_float_unsigned);

#[cfg(not(feature = "num-bigint"))]
to_primitive_small!(u8 i8 u16 i16 u32 i32);

#[cfg(all(target_pointer_width = "32", not(feature = "num-bigint")))]
to_primitive_small!(usize isize);

#[cfg(not(feature = "num-bigint"))]
macro_rules! to_primitive_64 {
    ($($type_name:ty)*) => ($(
        impl ToPrimitive for Rational32<$type_name> {
            fn to_i64(&self) -> Option<i64> {
                self.to_integer().to_i64()
            }

            fn to_i128(&self) -> Option<i128> {
                self.to_integer().to_i128()
            }

            fn to_u64(&self) -> Option<u64> {
                self.to_integer().to_u64()
            }

            fn to_u128(&self) -> Option<u128> {
                self.to_integer().to_u128()
            }

            fn to_f64(&self) -> Option<f64> {
                let float = ratio_to_f64(
                    self.numer as i128,
                    self.denom as i128
                );
                if float.is_nan() {
                    None
                } else {
                    Some(float)
                }
            }
        }
    )*)
}

#[cfg(not(feature = "num-bigint"))]
to_primitive_64!(u64 i64);

#[cfg(all(target_pointer_width = "64", not(feature = "num-bigint")))]
to_primitive_64!(usize isize);

trait Bits {
    fn bits(&self) -> u64;
}

impl Bits for i128 {
    fn bits(&self) -> u64 {
        (128 - self.wrapping_abs().leading_zeros()).into()
    }
}

/// Multiply `x` by 2 to the power of `exp`. Returns an accurate result even if `2^exp` is not
/// representable.
fn ldexp(x: f64, exp: i32) -> f64 {
    use core::f64::{INFINITY, MANTISSA_DIGITS, MAX_EXP, RADIX};

    assert_eq!(
        RADIX, 2,
        "only floating point implementations with radix 2 are supported"
    );

    const EXPONENT_MASK: u64 = 0x7ff << 52;
    const MAX_UNSIGNED_EXPONENT: i32 = 0x7fe;
    const MIN_SUBNORMAL_POWER: i32 = MANTISSA_DIGITS as i32;

    if x.is_zero() || x.is_infinite() || x.is_nan() {
        return x;
    }

    // Filter out obvious over / underflows to make sure the resulting exponent fits in an isize.
    if exp > 3 * MAX_EXP {
        return INFINITY * x.signum();
    } else if exp < -3 * MAX_EXP {
        return 0.0 * x.signum();
    }

    // curr_exp is the x's *biased* exponent, and is in the [-54, MAX_UNSIGNED_EXPONENT] range.
    let (bits, curr_exp) = if !x.is_normal() {
        // If x is subnormal, we make it normal by multiplying by 2^53. This causes no loss of
        // precision or rounding.
        let normal_x = x * 2f64.powi(MIN_SUBNORMAL_POWER);
        let bits = normal_x.to_bits();
        // This cast is safe because the exponent is at most 0x7fe, which fits in an i32.
        (
            bits,
            ((bits & EXPONENT_MASK) >> 52) as i32 - MIN_SUBNORMAL_POWER,
        )
    } else {
        let bits = x.to_bits();
        let curr_exp = (bits & EXPONENT_MASK) >> 52;
        // This cast is safe because the exponent is at most 0x7fe, which fits in an i32.
        (bits, curr_exp as i32)
    };

    // The addition can't overflow because exponent is between 0 and 0x7fe, and exp is between
    // -2*MAX_EXP and 2*MAX_EXP.
    let new_exp = curr_exp + exp;

    if new_exp > MAX_UNSIGNED_EXPONENT {
        INFINITY * x.signum()
    } else if new_exp > 0 {
        // Normal case: exponent is not too large nor subnormal.
        let new_bits = (bits & !EXPONENT_MASK) | ((new_exp as u64) << 52);
        f64::from_bits(new_bits)
    } else if new_exp >= -(MANTISSA_DIGITS as i32) {
        // Result is subnormal but may not be zero.
        // In this case, we increase the exponent by 54 to make it normal, then multiply the end
        // result by 2^-53. This results in a single multiplication with no prior rounding error,
        // so there is no risk of double rounding.
        let new_exp = new_exp + MIN_SUBNORMAL_POWER;
        debug_assert!(new_exp >= 0);
        let new_bits = (bits & !EXPONENT_MASK) | ((new_exp as u64) << 52);
        f64::from_bits(new_bits) * 2f64.powi(-MIN_SUBNORMAL_POWER)
    } else {
        // Result is zero.
        return 0.0 * x.signum();
    }
}
