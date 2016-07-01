/********************************************************************/
//! `bit_store` `bit_store-example.rs`

/********************************************************************/

extern crate bit_store;
use bit_store::*;

extern crate typenum;
use typenum::consts::*;

//extern crate generic_array;
//use generic_array::GenericArray;

fn main () {
  println!("bit_store example main...");

  let bytes = [
    0b_0011_0010_u8,
    0b_1010_0000_u8,
    0b_1111_0110_u8,
    0b_0001_1011_u8 ];
  let bs1 = BitStore::<u8,U4>::from_slice (&bytes);

  println!("bs1:\n{}", bs1);

  let bsshl = bs1 << 10;
  println!("bs1 << 10:\n{}", bsshl);

  let bsshr = bs1 >> 10;
  println!("bs1 >> 10:\n{}", bsshr);

  println!{"iterating bs1 bits..."}

  for i in bs1.iter() {
    println!{"{:?}", i};
  }

  println!("debug print bs1:\n{:?}", bs1);

  let bs32 = BitStore::<u32,U4>::from_slice (&[
    0b_10110010_00100001_00000010_01100010_u32,
    0b_00110100_00000100_10000000_00101010_u32,
    0b_10110100_01100011_11110100_11111011_u32,
    0b_00001111_11111100_10000000_00000000_u32]);

  println!("debug print bs32:\n{:?}", bs32);

  let bs1 = BitStore::<u32,U4>::mask_range (72..109);
  let bs2 = BitStore::<u32,U4>::mask_range (100..128);
  let bs1and2 = bs1 & bs2;
  let bs1or2 = bs1 | bs2;
  let bs1xor2 = bs1 ^ bs2;

  println!("bs1:\n{}", bs1);
  println!("bs2:\n{}", bs2);
  println!("bs1and2:\n{}", bs1and2);
  println!("bs1or2:\n{}", bs1or2);
  println!("bs1xor2:\n{}", bs1xor2);

  println!("...bit_store example main");
}
