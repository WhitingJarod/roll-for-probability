use crate::Rational32 as Ratio;

use core::cmp;
use num_traits::{One, Pow};

type T = i32;

macro_rules! pow_unsigned_impl {
    (@ $exp:ty) => {
        type Output = Ratio;
        #[inline]
        fn pow(self, expon: $exp) -> Ratio {
            Ratio::new_raw(self.numer.pow(expon as u32), self.denom.pow(expon as u32))
        }
    };
    ($exp:ty) => {
        impl Pow<$exp> for Ratio {
            pow_unsigned_impl!(@ $exp);
        }
        impl<'a> Pow<$exp> for &'a Ratio
        where
            &'a T: Pow<$exp, Output = T>,
        {
            pow_unsigned_impl!(@ $exp);
        }
        impl<'b> Pow<&'b $exp> for Ratio {
            type Output = Ratio;
            #[inline]
            fn pow(self, expon: &'b $exp) -> Ratio {
                Pow::pow(self, *expon)
            }
        }
        impl<'a, 'b> Pow<&'b $exp> for &'a Ratio
        where
            &'a T: Pow<$exp, Output = T>,
        {
            type Output = Ratio;
            #[inline]
            fn pow(self, expon: &'b $exp) -> Ratio {
                Pow::pow(self, *expon)
            }
        }
    };
}
pow_unsigned_impl!(u8);
pow_unsigned_impl!(u16);
pow_unsigned_impl!(u32);
pow_unsigned_impl!(u64);
pow_unsigned_impl!(u128);
pow_unsigned_impl!(usize);

macro_rules! pow_signed_impl {
    (@ $exp:ty, $unsigned:ty) => {
        type Output = Ratio;
        #[inline]
        fn pow(self, expon: $exp) -> Ratio {
            match expon.cmp(&0) {
                cmp::Ordering::Equal => One::one(),
                cmp::Ordering::Less => {
                    let expon = expon.wrapping_abs() as $unsigned;
                    Pow::pow(self, expon).into_recip()
                }
                cmp::Ordering::Greater => Pow::pow(self, expon as $unsigned),
            }
        }
    };
    ($exp:ty, $unsigned:ty) => {
        impl Pow<$exp> for Ratio {
            pow_signed_impl!(@ $exp, $unsigned);
        }
        impl<'a> Pow<$exp> for &'a Ratio
        where
            &'a T: Pow<$unsigned, Output = T>,
        {
            pow_signed_impl!(@ $exp, $unsigned);
        }
        impl<'b> Pow<&'b $exp> for Ratio {
            type Output = Ratio;
            #[inline]
            fn pow(self, expon: &'b $exp) -> Ratio {
                Pow::pow(self, *expon)
            }
        }
        impl<'a, 'b> Pow<&'b $exp> for &'a Ratio
        where
            &'a T: Pow<$unsigned, Output = T>,
        {
            type Output = Ratio;
            #[inline]
            fn pow(self, expon: &'b $exp) -> Ratio {
                Pow::pow(self, *expon)
            }
        }
    };
}
pow_signed_impl!(i8, u8);
pow_signed_impl!(i16, u16);
pow_signed_impl!(i32, u32);
pow_signed_impl!(i64, u64);
pow_signed_impl!(i128, u128);
pow_signed_impl!(isize, usize);
