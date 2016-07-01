/*******************************************************************/
//
//  bit_store crate
//
/*******************************************************************/

//! store and access bits by absolute and relative position

//! # Example
//!
//! ```
//! extern crate bit_store;
//! use bit_store::{
//!   Bit,
//!   BitMask,
//!   BitStore};
//!
//! extern crate typenum;
//! use typenum::consts::*;
//!
//! fn main () {
//!   let b = 0b_00001100_00101010_01000100_u32;
//!   assert_eq!(b.count_1s(), 7);
//!   assert_eq!(b.first(),         Some(Bit { abs:  2,  ord: 0 }));
//!   assert_eq!(b.last(),          Some(Bit { abs: 19,  ord: 6 }));
//!   assert_eq!(b.get_abs(6),      Some(Bit { abs:  6,  ord: 1 }));
//!   assert_eq!(b.get_ord(4),           Bit { abs: 13,  ord: 4 });
//!   assert_eq!(b.iter().nth(4),   Some(Bit { abs: 13,  ord: 4 }));
//!
//!   let bits = [
//!     0b_01000100_u8,
//!     0b_00101010_u8,
//!     0b_00001100_u8];
//!   let bs8 = BitStore::<u8,U3>::from_slice (&bits);
//!   assert_eq!(BitStore::<u8,U3>::size_bits(), 24);
//!   assert_eq!(b.count_1s(),    bs8.count_1s());
//!   assert_eq!(b.first(),       bs8.first());
//!   assert_eq!(b.last(),        bs8.last());
//!   assert_eq!(b.get_abs(6),    bs8.get_abs(6));
//!   assert_eq!(b.get_ord(4),    bs8.get_ord(4));
//!   assert_eq!(b.iter().nth(4), bs8.iter().nth(4));
//!
//!   let bs32 = BitStore::<u32,U2>::mask_range(20..40);
//!   assert_eq!(bs32.count_1s(), 20);
//!   assert_eq!(bs32[0], 0b_11111111_11110000_00000000_00000000_u32);
//!   assert_eq!(bs32[1], 0b_00000000_00000000_00000000_11111111_u32);
//!   assert_eq!(bs32 & BitStore::<u32,U2>::mask_range(15..25),
//!     BitStore::<u32,U2>::mask_range(20..25));
//!   assert_eq!(bs32 | BitStore::<u32,U2>::mask_range(15..25),
//!     BitStore::<u32,U2>::mask_range(15..40));
//!   assert_eq!(bs32 ^ BitStore::<u32,U2>::mask_range(15..25),
//!     BitStore::<u32,U2>::mask_range(15..20) |
//!     BitStore::<u32,U2>::mask_range(25..40));
//! }
//! ```

/*******************************************************************/

//
//  crate attributes
//

#![warn(unsafe_code)]
#![warn(missing_docs)]
#![warn(box_pointers)]
#![warn(fat_ptr_transmutes)]
#![warn(missing_copy_implementations)]
#![warn(missing_debug_implementations)]
#![warn(trivial_casts)]
#![warn(trivial_numeric_casts)]
#![warn(unused_extern_crates)]
#![warn(unused_import_braces)]
#![warn(unused_qualifications)]
#![warn(unused_results)]
#![warn(variant_size_differences)]

#![feature(zero_one)]
#![feature(const_fn)]

#![cfg_attr(test, feature(test))]
#![cfg_attr(test, feature(plugin))]
#![cfg_attr(test, feature(custom_attribute))]
#![cfg_attr(test, plugin(quickcheck_macros))]


//
//  imports
//

use std::fmt::{
  Display,
  Formatter,
  Result};
//use std::mem::size_of;
use std::num::{
  One,
  Zero};
use std::ops::{
  BitAnd,
  BitAndAssign,
  BitOr,
  BitOrAssign,
  BitXor,
  BitXorAssign,
  Deref,
  DerefMut,
  Not,
  //Range,
  Shl,
  ShlAssign,
  Shr,
  ShrAssign};

//extern crate typenum;
//use typenum::consts::*;

extern crate generic_array;
use generic_array::{
  ArrayLength,
  GenericArray};

extern crate num;
use num::{
  PrimInt,
  Unsigned};

pub mod bit_mask;
pub use bit_mask::{
  Bit,
  BitMask,
  Bix,
  Iter};



/*******************************************************************/
//
//  bit_store::Bits trait
//
/*******************************************************************/

/// trait for sub-units of a `BitStore`: unsigned integers with a
/// `BitMask` interface

pub trait Bits:
  BitMask +
  Default +
  PrimInt +
  Unsigned {}

impl Bits for u8    {}
impl Bits for u16   {}
impl Bits for u32   {}
impl Bits for u64   {}
impl Bits for usize {}



/*******************************************************************/
//
//  bit_store::BitStore struct
//
/*******************************************************************/

/// generic array of `Bits`, implementing the `BitMask` interface

#[derive(Clone,Copy,Debug,Eq,PartialEq)]
pub struct BitStore <T,N> where
  T            : Bits,
  N            : ArrayLength<T> + Copy + Eq,
  N::ArrayType : Copy
{

  /// generic array of `T:Bits`
  pub bits  :GenericArray<T,N>
}


/*******************************************************************/
//
//  bit_store::BitStore impl
//

impl <T,N> BitStore <T,N> where
  T            : Bits,
  N            : ArrayLength<T> + Copy + Eq,
  N::ArrayType : Copy
{

  ///////////////////////////////////////////////////////////////////
  //  static
  ///////////////////////////////////////////////////////////////////

  //
  //  bit_store::from_slice
  //
  /// construct from slice; sizes must be equal
  ///
  /// ```
  /// # extern crate typenum; use typenum::*;
  /// # extern crate bit_store; use bit_store::BitStore;
  /// # fn main () {
  /// let bytes = [ 0x40u8, 0x80u8, 0x20u8, 0x01u8  ];
  /// let bs = BitStore::<u8,U4>::from_slice (&bytes);
  /// assert_eq!(4, bs.len());
  /// # }
  /// ```

  /// # Panics
  ///
  /// sizes not equal:
  ///
  /// ```should_panic
  /// # extern crate typenum; use typenum::*;
  /// # extern crate bit_store; use bit_store::BitStore;
  /// # fn main () {
  /// let bytes = [ 0x40u8, 0x80u8 ];
  /// let bs = BitStore::<u8,U4>::from_slice (&bytes);
  /// # }
  /// ```

  pub fn from_slice (slice:&[T]) -> Self {
    BitStore::<T,N> { bits: GenericArray::from_slice(slice) }
  }


  ///////////////////////////////////////////////////////////////////
  //  self
  ///////////////////////////////////////////////////////////////////

  //
  //  bit_store::to_slice
  //
  /// derefernce coercion to `T` slice

  pub fn to_slice (&self) -> &[T] {
    &*self
  }

} // end impl bit_store::BitStore


/*******************************************************************/
//
//  bit_store::BitStore impl traits
//

/////////////////////////////////////////////////////////////////////
//  local
/////////////////////////////////////////////////////////////////////

//
//  BitStore:BitMask
//

impl <T,N> BitMask for BitStore <T,N> where
  T            : Bits,
  N            : ArrayLength<T> + Copy + Eq,
  N::ArrayType : Copy
{

  fn count_1s (&self) -> Bix {
    self.bits.iter().fold(0, |acc, ref i| acc + i.count_1s())
  }

  fn leading_0s (&self) -> Bix {
    let mut out:Bix = 0;
    for i in self.bits.iter().rev() {
      let x = i.leading_0s();
      out += x;
      if x < T::size_bits() {
        return out
      }
    };
    out
  }

  fn trailing_0s (&self) -> Bix {
    let mut out:Bix = 0;
    for i in self.bits.iter() {
      let x = i.trailing_0s();
      out += x;
      if x < T::size_bits() {
        return out
      }
    };
    out
  }


  ///////////////////////////////////////////////////////////////////
  //  override default
  ///////////////////////////////////////////////////////////////////

  fn show_bits (&self) -> String {
    let mut xs = String::new();
    let sep = if T::size_bits() == 8 {
      " "
    } else {
      "\n"
    };
    for i in self.bits.iter() {
      xs = xs + &i.show_bits() + sep;
    }
    let _ = xs.pop(); // unused result
    xs
  }

}


/////////////////////////////////////////////////////////////////////
//  extern
/////////////////////////////////////////////////////////////////////

//
//  BitStore:BitAnd
//

impl <T,N> BitAnd for BitStore <T,N> where
  T            : Bits,
  N            : ArrayLength<T> + Copy + Eq,
  N::ArrayType : Copy
{

  type Output = Self;

  fn bitand (self, rhs:Self) -> Self {
    let zs:Vec<_> = self.bits.iter().zip(rhs.bits.iter()).map(
      |(a,b)| *a & *b).collect();
    Self::from_slice (zs.as_slice())
  }
}


//
//  BitStore:BitAndAssign
//

impl <T,N> BitAndAssign for BitStore <T,N> where
  T            : Bits,
  N            : ArrayLength<T> + Copy + Eq,
  N::ArrayType : Copy
{

  fn bitand_assign (&mut self, rhs:Self) {
    *self = *self & rhs;
  }
}


//
//  BitStore:BitOr
//

impl <T,N> BitOr for BitStore <T,N> where
  T            : Bits,
  N            : ArrayLength<T> + Copy + Eq,
  N::ArrayType : Copy
{

  type Output = Self;

  fn bitor (self, rhs:Self) -> Self {
    let zs:Vec<_> = self.bits.iter().zip(rhs.bits.iter()).map(
      |(a,b)| *a | *b).collect();
    Self::from_slice (zs.as_slice())
  }
}


//
//  BitStore:BitOrAssign
//

impl <T,N> BitOrAssign for BitStore <T,N> where
  T            : Bits,
  N            : ArrayLength<T> + Copy + Eq,
  N::ArrayType : Copy
{

  fn bitor_assign (&mut self, rhs:Self) {
    *self = *self | rhs;
  }
}


//
//  BitStore:BitXor
//

impl <T,N> BitXor for BitStore <T,N> where
  T            : Bits,
  N            : ArrayLength<T> + Copy + Eq,
  N::ArrayType : Copy
{

  type Output = Self;

  fn bitxor (self, rhs:Self) -> Self {
    let zs:Vec<_> = self.bits.iter().zip(rhs.bits.iter()).map(
      |(a,b)| *a ^ *b).collect();
    Self::from_slice (zs.as_slice())
  }
}


//
//  BitStore:BitXorAssign
//

impl <T,N> BitXorAssign for BitStore <T,N> where
  T            : Bits,
  N            : ArrayLength<T> + Copy + Eq,
  N::ArrayType : Copy
{

  fn bitxor_assign (&mut self, rhs:Self) {
    *self = *self ^ rhs;
  }
}


//
//  BitStore:Deref
//

impl <T,N> Deref for BitStore <T,N> where
  T            : Bits,
  N            : ArrayLength<T> + Copy + Eq,
  N::ArrayType : Copy
{

  type Target = [T];

  fn deref (&self) -> &[T] {
    self.bits.deref()
  }
}


//
//  BitStore:DerefMut
//

impl <T,N> DerefMut for BitStore <T,N> where
  T            : Bits,
  N            : ArrayLength<T> + Copy + Eq,
  N::ArrayType : Copy
{

  fn deref_mut (&mut self) -> &mut [T] {
    self.bits.deref_mut()
  }
}


//
//  BitStore:Display
//

impl <T,N> Display for BitStore <T,N> where
  T            : Bits,
  N            : ArrayLength<T> + Copy + Eq,
  N::ArrayType : Copy
{

  fn fmt (&self, f:&mut Formatter) -> Result {
    write!(f, "{}", self.show_bits())
  }
}


//
//  BitStore:Not
//

impl <T,N> Not for BitStore <T,N> where
  T            : Bits,
  N            : ArrayLength<T> + Copy + Eq,
  N::ArrayType : Copy
{

  type Output = Self;

  fn not (self) -> Self {
    let zs:Vec<_> = self.bits.iter().map(|i| !*i).collect();
    Self::from_slice (zs.as_slice())
  }
}


//
//  BitStore:One
//

impl <T,N> One for BitStore <T,N> where
  T            : Bits,
  N            : ArrayLength<T> + Copy + Eq,
  N::ArrayType : Copy
{

  fn one () -> Self {
    let mut out = Self::zero();
    out.bits[0] = <T as One>::one();
    out
  }
}


//
//  BitStore:Shl
//

impl <T,N> Shl <Bix> for BitStore <T,N> where
  T            : Bits,
  N            : ArrayLength<T> + Copy + Eq,
  N::ArrayType : Copy
{

  type Output = Self;

  //
  // BitStore:Shl::shl
  //
  /// # Panics
  ///
  /// shift overflow:
  ///
  /// ```should_panic
  /// # extern crate typenum; use typenum::*;
  /// # extern crate bit_store; use bit_store::BitStore;
  /// # fn main () {
  /// let bytes = [ 0u8, 0u8, 0u8, 0u8 ];
  /// let bs = BitStore::<u8,U4>::from_slice (&bytes);
  /// let bshift = bs << 32;
  /// # }
  /// ```

  fn shl (self, rhs:Bix) -> Self {
    let len = N::to_usize();
    let tcap = T::size_bits();
    if rhs == 0 {
      return self;
    } else if Self::size_bits() < rhs {
      panic!("ERROR: BitStore << overflow");
    }

    let tshift = rhs / tcap;
    let lshift = rhs % tcap;
    let rshift = (tcap - lshift) % tcap;
    let mut out = GenericArray::<T,N>::new();

    out[tshift] = self[0] << lshift;
    for i in (tshift + 1)..len {
      let y = self[i-tshift];
      let x = self[i-tshift-1];
      out[i] = (y << lshift) | (x >> rshift);
    }
    BitStore::<T,N> { bits: out }
  }
}


//
//  BitStore:ShlAssign
//

impl <T,N> ShlAssign <Bix> for BitStore <T,N> where
  T            : Bits,
  N            : ArrayLength<T> + Copy + Eq,
  N::ArrayType : Copy
{

  fn shl_assign (&mut self, rhs:Bix) {
    *self = *self << rhs;
  }
}


//
//  BitStore:Shr
//

impl <T,N> Shr <Bix> for BitStore <T,N> where
  T            : Bits,
  N            : ArrayLength<T> + Copy + Eq,
  N::ArrayType : Copy
{

  type Output = Self;

  //
  // BitStore:Shr::shr
  //
  /// # Panics
  ///
  /// shift overflow:
  ///
  /// ```should_panic
  /// # extern crate typenum; use typenum::*;
  /// # extern crate bit_store; use bit_store::BitStore;
  /// # fn main () {
  /// let bytes = [ 0u8, 0u8, 0u8, 0u8 ];
  /// let bs = BitStore::<u8,U4>::from_slice (&bytes);
  /// let bshift = bs >> 32;
  /// # }
  /// ```

  fn shr (self, rhs:Bix) -> Self {
    let len = N::to_usize();
    let tcap = T::size_bits();
    if rhs == 0 {
      return self;
    } else if Self::size_bits() < rhs {
      panic!("ERROR: BitStore << overflow");
    }

    let tshift = rhs / tcap;
    let rshift = rhs % tcap;
    let lshift = (tcap - rshift) % tcap;
    let mut out = GenericArray::<T,N>::new();

    out[len-1 - tshift] = self[len-1] >> rshift;
    for i in (tshift + 1)..len {
      let j = len-1 - i;
      let y = self[j+tshift+1];
      let x = self[j+tshift];
      out[j] = (y << lshift) | (x >> rshift);
    }
    BitStore::<T,N> { bits: out }
  }
}


//
//  BitStore:ShrAssign
//

impl <T,N> ShrAssign <Bix> for BitStore <T,N> where
  T            : Bits,
  N            : ArrayLength<T> + Copy + Eq,
  N::ArrayType : Copy
{

  fn shr_assign (&mut self, rhs:Bix) {
    *self = *self >> rhs;
  }
}


//
//  BitStore:Zero
//

impl <T,N> Zero for BitStore <T,N> where
  T            : Bits,
  N            : ArrayLength<T> + Copy + Eq,
  N::ArrayType : Copy
{

  fn zero () -> Self {
    BitStore::<T,N> { bits: GenericArray::<T,N>::new() }
  }
}

//  end traits bit_store::BitStore



/******************************************************************/
//
//  bit_store::tests module
//
/******************************************************************/

#[cfg(test)]
extern crate quickcheck;

#[cfg(test)]
extern crate test;

#[cfg(test)]
mod tests {
  use super::*;

  extern crate typenum;
  use self::typenum::consts::*;



/******************************************************************/
//  bit_store::BitStore unit test

  #[test]
  fn bitstore_unit () {

    let bytes = [
      0b_0011_0010_u8,
      0b_1010_0000_u8,
      0b_1111_0110_u8,
      0b_0001_1011_u8 ];
    let bs1 = BitStore::<u8,U4>::from_slice (&bytes);

    assert_eq!(15, bs1.count_1s());
    assert_eq!(1, bs1.trailing_0s());
    assert_eq!(3, bs1.leading_0s());
    assert_eq!(Some(Bit { abs: 1, ord: 0 }), bs1.first());
    assert_eq!(Some(Bit { abs: 28, ord: 14 }), bs1.last());
    assert_eq!(Bit { abs: 15, ord: 5 }, bs1.get_ord(5));

    //
    // shl 10
    //

    let bytes = [
      0b_0000_0000_u8,
      0b_1100_1000_u8,
      0b_1000_0000_u8,
      0b_1101_1010_u8 ];
    let bs2 = BitStore::<u8,U4>::from_slice (&bytes);

    let bshift = bs1 << 10;
    assert_eq!(bshift, bs2);

    //
    // shr 10
    //

    let bytes = [
      0b_1010_1000_u8,
      0b_1111_1101_u8,
      0b_0000_0110_u8,
      0b_0000_0000_u8 ];
    let bs2 = BitStore::<u8,U4>::from_slice (&bytes);

    let bshift = bs1 >> 10;
    assert_eq!(bshift, bs2);

  } // end bit_store::BitStore unit



/*******************************************************************/
//  bit_store::BitStore quickcheck tests

#[cfg(test)]
mod bitstore_quickcheck {

  //use super::*;
  //use typenum::consts::*;

  // TODO: BitStore needs an Arbitrary implementation

} // end BitStore quickcheck



/*******************************************************************/
//  bit_store::BitStore bench tests

#[cfg(test)]
mod bitstore_bench {
  //use super::*;
  //use test::{Bencher,black_box};

} // end BitStore bench

} // end mod bit_store::tests
