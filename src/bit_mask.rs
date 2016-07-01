/*******************************************************************/
//
//  bit_mask module
//
/*******************************************************************/

//! `BitMask` interface, bit types and iterators


//
//  imports
//

extern crate std;
//use std::fmt::Display;
use std::mem::
  size_of;
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
  Not,
  Range,
  Shl,
  ShlAssign,
  Shr,
  ShrAssign};



/*******************************************************************/
//
//  bit_mask::Bix type
//
/*******************************************************************/

/// used throughout as the index type of bit operations

pub type Bix = usize;



/*******************************************************************/
//
//  bit_mask::Bit struct
//
/*******************************************************************/

/// indicates an ordinal and absolute `Bix` position of a `1` bit in
/// a `BitMask`

/// # Examples
///
/// get a `Bit` from a `BitMask` type:
///
/// ```
/// # use bit_store::bit_mask::{Bit,BitMask};
/// let b:u8 = 0b_0110_1100_u8;
/// assert_eq!(Some(Bit { abs: 3, ord: 1 }), b.get_abs(3));
/// assert_eq!(Bit { abs: 6, ord: 3 }, b.get_ord(3));
/// ```

#[derive(Clone,Copy,Debug,Default,Eq,PartialEq)]
pub struct Bit {
  /// absolute position of `Bit` in `Bits`
  pub abs :Bix,
  /// relative position of `Bit` in `Bits`
  pub ord :Bix
}



/*******************************************************************/
//
//  bit_mask::BitMask trait
//
/*******************************************************************/

/// interface for collections of bits

pub trait BitMask:
  BitAnd        <Self, Output=Self> +
  BitAndAssign  <Self> +
  BitOr         <Self, Output=Self> +
  BitOrAssign   <Self> +
  BitXor        <Self, Output=Self> +
  BitXorAssign  <Self> +
  Copy +
  Eq +
  Not           <Output=Self> +
  One +
  Shl           <Bix, Output=Self> +
  ShlAssign     <Bix> +
  Shr           <Bix, Output=Self> +
  ShrAssign     <Bix> +
  Zero
{
  ///////////////////////////////////////////////////////////////////
  // required
  ///////////////////////////////////////////////////////////////////

  //
  //  BitMask::count_1s
  //
  /// count `1`s
  fn count_1s (&self) -> Bix;

  //
  //  BitMask::leading_0s
  //
  /// leading `0`s
  fn leading_0s (&self) -> Bix;

  //
  //  BitMask::trailing_0s
  //
  /// trailing `0`s
  fn trailing_0s (&self) -> Bix;


  ///////////////////////////////////////////////////////////////////
  //  provided static
  ///////////////////////////////////////////////////////////////////

  //
  //  BitMask::empty
  //
  /// empty bitmask

  fn empty () -> Self {
    Self::zero()
  }


  //
  //  BitMask::mask_bit
  //
  /// bitmask with a single bit set
  ///
  /// ```
  /// # use bit_store::bit_mask::BitMask;
  /// assert_eq!(0b_0010_0000_u8, u8::mask_bit(5));
  /// assert_eq!(0b_1000_0000_u8, u8::mask_bit(7));
  /// assert_eq!(0b_0000_0001_u8, u8::mask_bit(0));
  /// ```

  /// # Panics
  ///
  /// `abs` greater than or equal to `capacity`:
  ///
  /// ```should_panic
  /// # use bit_store::bit_mask::BitMask;
  /// let b = u8::mask_bit(8);
  /// ```

  fn mask_bit (abs:Bix) -> Self {
    Self::pow2(abs)
  }


  //
  //  BitMask::mask_range
  //
  /// bitmask with a non-empty range of bits set to `1`
  ///
  /// a range `y..x` with `range.end <= range.start` is the
  /// bitwise inverse of `x..(y+1)`
  ///
  /// ```
  /// # use bit_store::bit_mask::BitMask;
  /// assert_eq!(0b_1111_1111_u8, u8::mask_range(0..8));
  /// assert_eq!(0b_0011_1100_u8, u8::mask_range(2..6));
  /// assert_eq!(0b_0000_0100_u8, u8::mask_range(2..3));
  /// assert_eq!(0b_1111_1011_u8, u8::mask_range(2..2));
  /// assert_eq!(0b_1100_0011_u8, u8::mask_range(5..2));
  /// ```
  ///
  /// # Panics
  ///
  /// `range.start` greater than or equal to capacity:
  ///
  /// ```should_panic
  /// # use bit_store::bit_mask::BitMask;
  /// println!("{:?}", u8::mask_range(8..5)); // panic
  /// ```
  ///
  /// `range.end` greater than capacity:
  ///
  /// ```should_panic
  /// # use bit_store::bit_mask::BitMask;
  /// println!("{:?}", u8::mask_range(5..9)); // panic
  /// ```

  fn mask_range (range:Range<Bix>) -> Self {
    assert!(range.start < Self::size_bits());
    assert!(range.end <= Self::size_bits());
    if range.end <= range.start {
      !Self::mask_range (range.end..(range.start + 1))
    } else {
      let mut out = !Self::zero();
      out >>= Self::size_bits() - range.len();
      out <<= range.start;
      out
    }
  }


  //
  //  BitMask::mask_unbit
  //
  /// bitmask of `1`s with a single `0` bit set
  ///
  /// ```
  /// # use bit_store::bit_mask::BitMask;
  /// assert_eq!(0b_1101_1111_u8, u8::mask_unbit(5));
  /// assert_eq!(0b_0111_1111_u8, u8::mask_unbit(7));
  /// assert_eq!(0b_1111_1110_u8, u8::mask_unbit(0));
  /// ```

  /// # Panics
  ///
  /// `abs` greater than or equal to `capacity`:
  ///
  /// ```should_panic
  /// # use bit_store::bit_mask::BitMask;
  /// let b = u8::mask_unbit(8);
  /// ```

  fn mask_unbit (abs:Bix) -> Self {
    !Self::pow2(abs)
  }


  //
  //  BitMask::pow2
  //
  /// `2^exp` operation using `<<`; much faster than `2.pow(exp)`
  ///
  /// ```
  /// # use bit_store::bit_mask::BitMask;
  /// let b:u8 = 0b_0010_0000_u8;
  /// assert_eq!(b, u8::pow2(5));
  /// ```

  /// # Panics
  ///
  /// shift bits overflow for `exp` greater than or equal to
  /// `capacity`:
  ///
  /// ```should_panic
  /// # use bit_store::bit_mask::BitMask;
  /// let b = u8::pow2(8);
  /// ```

  fn pow2 (exp:Bix) -> Self {
    Self::one() << exp
  }


  //
  //  BitMask::size_bits
  //
  /// size in bits
  ///
  /// ```
  /// # use bit_store::bit_mask::BitMask;
  /// assert_eq!(8, u8::size_bits());
  /// ```

  fn size_bits () -> Bix {
    8*size_of::<Self>() //as Bix
  }


  ///////////////////////////////////////////////////////////////////
  //  provided self
  ///////////////////////////////////////////////////////////////////

  //
  //  BitMask::contains
  //
  /// checks for active bit (absolute position)
  ///
  /// ```
  /// # use bit_store::bit_mask::BitMask;
  /// let b:u8 = 0b_0001_1110_u8;
  /// assert!(b.contains(4));
  /// assert!(!b.contains(5));
  /// ```

  /// # Panics
  ///
  /// `abs` greater than or equal to capcity:
  ///
  /// ```should_panic
  /// # use bit_store::bit_mask::BitMask;
  /// let b:u8 = 0b_0010_0110_u8;
  /// println!("b contains? 10: {}", b.contains(10));
  /// ```

  fn contains (&self, abs:Bix) -> bool {
    assert!(abs < Self::size_bits());
    let b = Self::mask_bit(abs);
    *self & b != Self::zero()
  }


  //
  //  BitMask::first
  //
  /// least significant bit
  ///
  /// ```
  /// # use bit_store::bit_mask::{Bit,BitMask};
  /// let b:u8 = 0b_0001_1110_u8;
  /// assert_eq!(Some(Bit { abs: 1, ord: 0 }), b.first());
  /// ```

  fn first (&self) -> Option<Bit> {
    let zs = self.trailing_0s();
    let sz = Self::size_bits();
    if zs == sz {
      None
    } else {
      Some (Bit {
        abs: zs,
        ord: 0 })
    }
  }


  //
  //  BitMask::get_abs
  //
  /// get bit if it is contained or else `None`
  ///
  /// ```
  /// # use bit_store::bit_mask::{Bit,BitMask};
  /// let b:u8 = 0b_0011_0010_u8;
  /// assert_eq!(None, b.get_abs(0));
  /// assert_eq!(Some(Bit { abs: 1, ord: 0 }), b.get_abs(1));
  /// assert_eq!(None, b.get_abs(2));
  /// assert_eq!(None, b.get_abs(3));
  /// assert_eq!(Some(Bit { abs: 4, ord: 1 }), b.get_abs(4));
  /// assert_eq!(Some(Bit { abs: 5, ord: 2 }), b.get_abs(5));
  /// assert_eq!(None, b.get_abs(6));
  /// assert_eq!(None, b.get_abs(7));
  /// ```

  /// # Panics
  ///
  /// `abs` greater than or equal to `size_bits`:
  ///
  /// ```should_panic
  /// # use bit_store::bit_mask::BitMask;
  /// let b:u8 = 0b_0011_0110_u8;
  /// println!("b get abs 10: {:?}", b.get_abs(10));
  /// ```

  fn get_abs (&self, abs:Bix) -> Option<Bit> {
    assert!(abs < Self::size_bits());
    if self.contains(abs) {
      let mut mbits = *self;
      let mut ord;
      let half = Self::size_bits() / 2;
      if abs < half {
        // forward search: right shift
        ord = 0;
        let mut shift_count = 0;
        let shift = mbits.trailing_0s() + 1;
        shift_count += shift;
        mbits >>= shift;
        while shift_count <= abs {
          let shift = mbits.trailing_0s() + 1;
          shift_count += shift;
          mbits >>= shift;
          ord += 1;
        }
      } else {
        // reverse search: left shift
        ord = self.count_1s();
        let mut shift_count = Self::size_bits();
        while abs < shift_count {
          let shift = self.leading_0s() + 1;
          shift_count -= shift;
          mbits <<= shift;
          ord -= 1;
        }
      }
      Some(Bit {
        abs: abs,
        ord: ord })
    } else {
      None
    }
  }


  //
  //  BitMask::get_ord
  //
  /// get bit by ordinal position
  ///
  /// ```
  /// # use bit_store::bit_mask::{Bit,BitMask};
  /// let b:u8 = 0b_0011_0110_u8;
  /// assert_eq!(Bit { abs: 1, ord: 0 }, b.get_ord(0));
  /// assert_eq!(Bit { abs: 2, ord: 1 }, b.get_ord(1));
  /// assert_eq!(Bit { abs: 4, ord: 2 }, b.get_ord(2));
  /// assert_eq!(Bit { abs: 5, ord: 3 }, b.get_ord(3));
  /// ```

  /// # Panics
  ///
  /// `ord` greater than or equal to `len`:
  ///
  /// ```should_panic
  /// # use bit_store::bit_mask::BitMask;
  /// let b:u8 = 0b_0011_0110_u8;
  /// println!("b get ord 4: {:?}", b.get_ord(4));
  /// ```

  fn get_ord (&self, ord:Bix) -> Bit {
    assert!(ord < self.count_1s());

    let len = self.count_1s();
    let half = self.count_1s() / 2;
    let mut mbits = *self;
    let mut abs;
    let mut o;
    if ord  == 0 {
      abs = self.trailing_0s();

    } else if ord == len - 1 {
      abs = Self::size_bits() - self.leading_0s() - 1;

    } else if ord < half {
      // forward search: right shift
      o = 0;
      let mut a = mbits.trailing_0s();
      abs = a;
      mbits >>= a + 1;
      while o < ord {
        a = mbits.trailing_0s() + 1;
        mbits >>= a;
        abs += a;
        o += 1;
      }

    } else {
      // reverse search: left shift
      o = self.count_1s();
      abs = Self::size_bits();
      while ord < o {
        let a = mbits.leading_0s() + 1;
        mbits <<= a;
        abs -= a;
        o -= 1;
      }
    }

    Bit {
      abs: abs,
      ord: ord }
  }


  //
  //  BitMask::insert_abs
  //
  /// insert `1` (absolute position)
  ///
  /// ```
  /// # use bit_store::bit_mask::{Bit,BitMask};
  /// let mut b:u8 = 0b_0010_1010_u8;
  /// assert_eq!(0b_0010_1110_u8, *b.insert_abs(2));
  /// assert_eq!(0b_0011_1110_u8, *b.insert_abs(4));
  /// ```

  /// # Panics
  ///
  /// `abs` already contained:
  ///
  /// ```should_panic
  /// # use bit_store::bit_mask::BitMask;
  /// let mut b:u8 = 0b_0011_0110_u8;
  /// println!("b insert 1: {:?}", *b.insert_abs(1));
  /// ```
  ///
  /// `abs` greater than or equal to `capacity`:
  ///
  /// ```should_panic
  /// # use bit_store::bit_mask::BitMask;
  /// let mut b:u8 = 0b_0011_0110_u8;
  /// println!("b insert 10: {:?}", *b.insert_abs(10));
  /// ```

  fn insert_abs (&mut self, abs:Bix) -> &mut Self {
    assert!(!self.contains(abs));
    *self |= Self::mask_bit(abs);
    self
  }


  //
  //  BitMask::is_empty
  //
  /// all `0`s
  ///
  /// ```
  /// # #![feature(zero_one)]
  /// # use bit_store::bit_mask::BitMask;
  /// # use std::num::Zero;
  /// let b:u8 = 0u8;
  /// assert!(b.is_empty());
  /// assert!(u8::empty().is_empty());
  /// assert!(!u8::mask_bit(5).is_empty());
  /// ```

  fn is_empty (&self) -> bool {
    *self == Self::empty()
  }


  //
  //  BitMask::iter
  //
  /// const iterator
  ///
  /// ```
  /// # use bit_store::bit_mask::{Bit,BitMask};
  /// let b:u8 = 0b_0001_1110_u8;
  /// let mut abs = 1;
  /// let mut ord = 0;
  /// for i in b.iter() {
  ///   assert_eq!(Bit { abs: abs, ord: ord }, i);
  ///   abs += 1;
  ///   ord += 1;
  /// }
  /// assert!(ord == b.count_1s());
  /// ```

  fn iter (&self) -> Iter<Self> {
    let len = self.count_1s();
    Iter::<Self> {
      bits: &self,
      left: *self,
      abs:  Self::size_bits(),
      rem:  len,
      len:  len
    }
  }


  //
  //  BitMask::last
  //
  /// most significant bit
  ///
  /// ```
  /// # use bit_store::bit_mask::{Bit,BitMask};
  /// let b:u8 = 0b_0001_1110_u8;
  /// assert_eq!(Some(Bit { abs: 4, ord: 3 }), b.last());
  /// ```

  fn last (&self) -> Option<Bit> {
    let zs = self.leading_0s();
    let sz = Self::size_bits();
    if zs == sz {
      None
    } else {
      Some (Bit {
        abs: sz - zs - 1,
        ord: self.count_1s() - 1 })
    }
  }


  //
  //  BitMask::raw_bytes
  //
  /// raw bytes
  ///
  /// ```
  /// # use bit_store::bit_mask::BitMask;
  /// let b:u16 = 0b_00100110_01010100_u16;
  /// let bs:&[u8] = b.raw_bytes();
  /// assert_eq!(bs[0], 0b_01010100_u8);
  /// assert_eq!(bs[1], 0b_00100110_u8);
  /// ```

  #[allow(unsafe_code)]
  fn raw_bytes (&self) -> &[u8] {
    let bp:*const u8 = unsafe { std::mem::transmute(self) };
    unsafe {
      std::slice::from_raw_parts(bp, size_of::<Self>())
    }
  }


  //
  //  BitMask::remove_abs
  //
  /// remove contained `1` (absolute position)
  ///
  /// ```
  /// # use bit_store::bit_mask::{Bit,BitMask};
  /// let mut b:u8 = 0b_0010_1110_u8;
  /// assert_eq!(0b_0010_1010_u8, *b.remove_abs(2));
  /// ```

  /// # Panics
  ///
  /// `abs` not contained:
  ///
  /// ```should_panic
  /// # use bit_store::bit_mask::BitMask;
  /// let mut b:u8 = 0b_0011_0110_u8;
  /// println!("b remove abs 3: {:?}", *b.remove_abs(3));  // panic
  /// ```
  ///
  /// `abs` greater than or equal to `capacity`:
  ///
  /// ```should_panic
  /// # use bit_store::bit_mask::BitMask;
  /// let mut b:u8 = 0b_0011_0110_u8;
  /// println!("b remove abs 10: {:?}", *b.remove_abs(10));  // panic
  /// ```

  fn remove_abs (&mut self, abs:Bix) -> &mut Self {
    assert!(self.contains(abs));
    *self &= Self::mask_unbit(abs);
    self
  }


  //
  //  BitMask::remove_ord
  //
  /// remove contained `1` (relative position)
  ///
  /// ```
  /// # use bit_store::bit_mask::{Bit,BitMask};
  /// let mut b:u8 = 0b_0010_1110_u8;
  /// assert_eq!(0b_0010_0110_u8, *b.remove_ord(2));
  /// ```

  /// # Panics
  ///
  /// `ord` greater than or equal to `len`:
  ///
  /// ```should_panic
  /// # use bit_store::bit_mask::BitMask;
  /// let mut b:u8 = 0b_0011_0110_u8;
  /// println!("b remove ord 4: {:?}", *b.remove_ord(4));  // panic
  /// ```

  fn remove_ord (&mut self, ord:Bix) -> &mut Self {
    assert!(ord < self.count_1s());
    let b = self.get_ord(ord);
    *self &= Self::mask_unbit(b.abs);
    self
  }


  //
  //  BitMask::show_bits
  //
  /// convert to a left-to-right string of bits grouped by individual
  /// bytes separated by spaces
  ///
  /// ```
  /// # use bit_store::bit_mask::BitMask;
  /// let b:u16 = 0b_00000001_00000001_u16;
  /// assert_eq!("10000000 10000000", b.show_bits());
  /// ```

  fn show_bits (&self) -> String {
    let mut xs = String::new();
    for i in self.raw_bytes() {
      let s = format!(" {:>08b}", i);
      let z:String = s.chars().rev().collect();
      xs = xs + &z;
    }
    let _ = xs.pop(); // unused result
    xs
  }
}


/*******************************************************************/
//
//  bit_mask::BitMask impl
//

//
//  u8:BitMask -- 1 byte
//

impl BitMask for u8 {
  fn count_1s (&self) -> Bix { self.count_ones() as Bix }
  fn leading_0s (&self) -> Bix { self.leading_zeros() as Bix }
  fn trailing_0s (&self) -> Bix { self.trailing_zeros() as Bix }
}


//
//  u16:BitMask -- 2 bytes
//

impl BitMask for u16 {
  fn count_1s (&self) -> Bix { self.count_ones() as Bix }
  fn leading_0s (&self) -> Bix { self.leading_zeros() as Bix }
  fn trailing_0s (&self) -> Bix { self.trailing_zeros() as Bix }
}


//
//  u32:BitMask -- 4 bytes
//

impl BitMask for u32 {
  fn count_1s (&self) -> Bix { self.count_ones() as Bix }
  fn leading_0s (&self) -> Bix { self.leading_zeros() as Bix }
  fn trailing_0s (&self) -> Bix { self.trailing_zeros() as Bix }
}


//
//  u64:BitMask -- 8 bytes
//

impl BitMask for u64 {
  fn count_1s (&self) -> Bix { self.count_ones() as Bix }
  fn leading_0s (&self) -> Bix { self.leading_zeros() as Bix }
  fn trailing_0s (&self) -> Bix { self.trailing_zeros() as Bix }
}


//
//  usize:BitMask -- native bytes
//

impl BitMask for usize {
  fn count_1s (&self) -> Bix { self.count_ones() as Bix }
  fn leading_0s (&self) -> Bix { self.leading_zeros() as Bix }
  fn trailing_0s (&self) -> Bix { self.trailing_zeros() as Bix }
}



/*******************************************************************/
//
//  bit_mask::Iter
//
/*******************************************************************/

/// `BitMask` iterator

#[derive(Clone,Copy,Debug)]
pub struct Iter <'a,T> where
  T : 'a + BitMask
{
  bits : &'a T,
  left : T,
  abs  : Bix,
  rem  : Bix,
  len  : Bix
}


//
//  Iter:Iterator
//

impl <'a,T> Iterator for Iter <'a,T> where
  T : BitMask
{
  type Item = Bit;

  fn next (&mut self) -> Option<Bit> {
    if self.rem == 0 {
      None
    } else {
      let o = self.len - self.rem;
      if let Some(Bit { abs: pos, ord: _ }) = self.left.first() {
        self.abs = pos;
        let _ = self.left.remove_abs(self.abs); // unused result
        self.rem -= 1;
        Some(Bit { ord: o, abs: self.abs })
      } else {
        unreachable!("ERROR: BitMask Iter found no bits left");
      }
    }
  }
}


/*******************************************************************/
//
//  bit_mask::tests module
//
/*******************************************************************/

#[cfg(test)]
extern crate quickcheck;

#[cfg(test)]
extern crate test;

#[cfg(test)]
mod tests {
  use super::*;


/*******************************************************************/
//  bit_mask::BitMask unit test

  #[test]
  fn bitmask_unit () {

    /////////////////////////////////////////////////////////////////
    // u8
    /////////////////////////////////////////////////////////////////

    assert_eq!(8, u8::size_bits());

    let b:u8 = 0b_0010_1001_u8;
    assert_eq!(3, b.count_1s());
    assert!(
      match b.first() {
        Some(Bit { abs: 0, ord: 0 }) => true,
        _       => false,
      }
    );
    assert!(
      match b.last() {
        Some(Bit { abs: 5, ord: 2 }) => true,
        _       => false,
      }
    );

    let b:u8 = 0b_0000_0000_u8;
    assert_eq!(0, b.count_1s());
    assert!(
      match b.first() {
        None => true,
        _    => false,
      }
    );
    assert!(
      match b.last() {
        None => true,
        _    => false,
      }
    );

    let b:u8 = 0b_1111_1111_u8;
    assert_eq!(8, b.count_1s());
    assert_eq!(0, (!b).count_1s());
    assert!(
      match b.first() {
        Some(Bit { abs: 0, ord: 0 }) => true,
        _       => false,
      }
    );
    assert!(
      match b.last() {
        Some(Bit { abs: 7, ord: 7 }) => true,
        _       => false,
      }
    );

    let b:u8 = 0b_1010_1100_u8;
    assert_eq!(Bit { abs: 2, ord: 0 }, b.get_ord(0));
    assert_eq!(Bit { abs: 3, ord: 1 }, b.get_ord(1));
    assert_eq!(Bit { abs: 5, ord: 2 }, b.get_ord(2));
    assert_eq!(Bit { abs: 7, ord: 3 }, b.get_ord(3));

    let b:u8 = 0b_0010_1101_u8;
    assert_eq!(Bit { abs: 0, ord: 0 }, b.get_ord(0));
    assert_eq!(Bit { abs: 2, ord: 1 }, b.get_ord(1));
    assert_eq!(Bit { abs: 3, ord: 2 }, b.get_ord(2));
    assert_eq!(Bit { abs: 5, ord: 3 }, b.get_ord(3));

    for i in 0..8 {
      assert_eq!(u8::mask_bit(i), !u8::mask_unbit(i));
    }

  } // end BitMask unit



/*******************************************************************/
//  bit_mask::BitMask quickcheck tests

#[cfg(test)]
mod bitmask_quickcheck {

  use super::super::*;

  ///////////////////////////////////////////////////////////////////
  // u8
  ///////////////////////////////////////////////////////////////////
  #[allow(trivial_casts)]
  #[quickcheck]
  fn insert_remove_abs_inverses_u8 (b:Bix) -> bool {
    let abs = b % u8::size_bits();
    let mut x = u8::empty();
    let mut y = u8::empty();
    *x.insert_abs(abs).remove_abs(abs) == u8::empty() &&
    *y.insert_abs(abs).remove_ord(0) == u8::empty()
  }

  #[allow(trivial_casts)]
  #[quickcheck]
  fn isempty_iff_len_eq0_u8 (bs:u8) -> bool {
    bs.is_empty() && 0 == bs.count_1s() ||
    !bs.is_empty() && 0 < bs.count_1s()
  }

} // end BitMask quickcheck



/*******************************************************************/
//  bit_mask::BitMask benchmark tests

#[cfg(test)]
mod bitmask_bench {

  use super::super::*;
  use test::{Bencher,black_box};

  #[bench]
  fn pow2_shl_u64 (b:&mut Bencher) {
    b.iter(|| {
      let n = black_box(1000);
      for _ in 0..n {
        for i in 0..64 {
          assert!(0 != u64::pow2(i));
        }
      }
    })
  }

  #[bench]
  fn pow2_pow_u64 (b:&mut Bencher) {
    b.iter(|| {
      let n = black_box(1000);
      for _ in 0..n {
        for i in 0..64 {
          assert!(0 != 2u64.pow(i));
        }
      }
    })
  }

  #[bench]
  fn pow2_wrap_u64 (b:&mut Bencher) {
    b.iter(|| {
      let n = black_box(1000);
      for _ in 0..n {
        for i in 64..128 {
          assert!(0 != 1u64.wrapping_shl(i));
        }
      }
    })
  }

} // end BitMask bench

} // end bit_mask::tests
