/********************************************************************/
//! `bit_store` `bit_mask-example.rs`

/********************************************************************/

extern crate bit_store;
use bit_store::bit_mask::*;

fn main () {
  println!("bit_mask example main...");

  let b8  :u8   = 0b_00001000_u8;
  let b16 :u16  = 0b_00000100_00001000_u16;
  let b32 :u32  = 0b_01011100_00000000_00000100_00001000_u32;

  println!("{}", b8.show_bits());
  println!("{}", b16.show_bits());
  println!("{}", b32.show_bits());

  for i in b8.iter() {
    println!("{:?}", i);
  }

  for i in b16.iter() {
    println!("{:?}", i);
  }

  for i in b32.iter() {
    println!("{:?}", i);
  }

  let b:u8 = u8::empty();
  println!("{}", b.show_bits());

  for i in b.iter() {
    println!("{:?}", i);
  }

  let b:u8 = 0xff;
  println!("{}", b.show_bits());

  for i in b.iter() {
    println!("{:?}", i);
  }

  let mut b:u8 = 0xff;
  println!("{}", b.show_bits());
  for _ in 0..8 {
    b <<= 1;
    println!("{}", b.show_bits());
  }

  let b:u8 = u8::mask_range (0..1);
  println!("{}", b.show_bits());

  let b:u8 = u8::mask_range (0..8);
  println!("{}", b.show_bits());

  let b:u8 = u8::mask_range (7..8);
  println!("{}", b.show_bits());

  let b:u8 = u8::mask_range (2..5);
  println!("{}", b.show_bits());

  let mut b:u8 = 0b_1110_1111_u8;
  println!("{}", b.show_bits());
  println!("get abs bit 4: {:?}", b.get_abs(4));
  println!("get abs bit 5: {:?}", b.get_abs(5));
  b <<= 4;
  b >>= 4;
  println!("{}", b.show_bits());

  let b:u8 = 0b_1010_1100_u8;
  println!("{}", b.show_bits());
  println!("get ord bit 0: {:?}", b.get_ord(0));
  println!("get ord bit 1: {:?}", b.get_ord(1));
  println!("get ord bit 2: {:?}", b.get_ord(2));
  println!("get ord bit 3: {:?}", b.get_ord(3));

  let b:u8 = 0b_0010_1101_u8;
  println!("{}", b.show_bits());
  println!("get ord bit 0: {:?}", b.get_ord(0));
  println!("get ord bit 1: {:?}", b.get_ord(1));
  println!("get ord bit 2: {:?}", b.get_ord(2));
  println!("get ord bit 3: {:?}", b.get_ord(3));

  let mut b:u8 = 0b_0010_1101_u8;
  println!("{}", b.show_bits());
  println!("b insert 1: {}", b.insert_abs(1).show_bits());
  println!("b remove abs 0: {}", b.remove_abs(0).show_bits());
  println!("b insert 0, remove abs 0: {}",
    b.insert_abs(0).remove_abs(0).show_bits());

  let b:u8 = 0b_0110_1100_u8;
  println!("{}", b.show_bits());
  println!("get abs bit 3: {:?}", b.get_abs(3));
  println!("get ord bit 3: {:?}", b.get_ord(3));

  println!("...bit_mask example main");
}
