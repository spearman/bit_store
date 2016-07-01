extern crate bit_store;
use bit_store::{
  Bit,
  BitMask,
  BitStore};

extern crate typenum;
use typenum::consts::*;

fn main () {
  let bits = [
    0b_01000100_u8,
    0b_00101010_u8,
    0b_00001100_u8];
  let bs8 = BitStore::<u8,U3>::from_slice (&bits);
  assert_eq!(BitStore::<u8,U3>::size_bits(), 24);
  assert_eq!(bs8.count_1s(), 7);
  assert_eq!(bs8.first(),       Some(Bit { abs:  2,  ord: 0 }));
  assert_eq!(bs8.last(),        Some(Bit { abs: 19,  ord: 6 }));
  assert_eq!(bs8.get_abs(6),    Some(Bit { abs:  6,  ord: 1 }));
  assert_eq!(bs8.get_ord(4),         Bit { abs: 13,  ord: 4 });
  assert_eq!(bs8.iter().nth(4), Some(Bit { abs: 13,  ord: 4 }));

  let bs32 = BitStore::<u32,U2>::mask_range(20..40);
  assert_eq!(bs32.count_1s(), 20);
  assert_eq!(bs32[0], 0b_11111111_11110000_00000000_00000000_u32);
  assert_eq!(bs32[1], 0b_00000000_00000000_00000000_11111111_u32);
  assert_eq!(bs32 & BitStore::<u32,U2>::mask_range(15..25),
    BitStore::<u32,U2>::mask_range(20..25));
  assert_eq!(bs32 | BitStore::<u32,U2>::mask_range(15..25),
    BitStore::<u32,U2>::mask_range(15..40));
  assert_eq!(bs32 ^ BitStore::<u32,U2>::mask_range(15..25),
    BitStore::<u32,U2>::mask_range(15..20) |
    BitStore::<u32,U2>::mask_range(25..40));
}
