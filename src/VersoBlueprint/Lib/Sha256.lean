/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

/-!
SHA-256 (FIPS 180-4), for naming a compiled module by its contents: the record of kernel replays
(`Informal.Stats.replayBuild`) must not take one file for another, so it does not use Lean's
64-bit `Hashable` hashes.
-/

namespace Informal.Sha256

private def roundConstants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

private def initialState : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

@[inline] private def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- The state after the 64-byte block of `data` at `offset` (which must be there). -/
private def compress (state : Array UInt32) (data : ByteArray) (offset : Nat) : Array UInt32 :=
  Id.run do
  let mut w : Array UInt32 := Array.mkEmpty 64
  for i in [0:16] do
    let b (j : Nat) : UInt32 := (data.get! (offset + 4 * i + j)).toUInt32
    w := w.push ((b 0 <<< 24) ||| (b 1 <<< 16) ||| (b 2 <<< 8) ||| b 3)
  for i in [16:64] do
    let x := w[i - 15]!
    let y := w[i - 2]!
    let s0 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
    let s1 := rotr y 17 ^^^ rotr y 19 ^^^ (y >>> 10)
    w := w.push (w[i - 16]! + s0 + w[i - 7]! + s1)
  let mut a := state[0]!
  let mut b := state[1]!
  let mut c := state[2]!
  let mut d := state[3]!
  let mut e := state[4]!
  let mut f := state[5]!
  let mut g := state[6]!
  let mut h := state[7]!
  for i in [0:64] do
    let s1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let t1 := h + s1 + ch + roundConstants[i]! + w[i]!
    let s0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := s0 + maj
    h := g; g := f; f := e; e := d + t1
    d := c; c := b; b := a; a := t1 + t2
  return #[state[0]! + a, state[1]! + b, state[2]! + c, state[3]! + d,
    state[4]! + e, state[5]! + f, state[6]! + g, state[7]! + h]

/-- The SHA-256 digest of `data`: 32 bytes. -/
def digest (data : ByteArray) : ByteArray := Id.run do
  let mut state := initialState
  let blocks := data.size / 64
  for i in [0:blocks] do
    state := compress state data (64 * i)
  -- the rest, a one bit, zeros, and the length in bits as 64 bits, most significant first
  let mut tail := data.extract (64 * blocks) data.size
  tail := tail.push 0x80
  while tail.size % 64 != 56 do
    tail := tail.push 0
  let bits := data.size * 8
  for i in [0:8] do
    tail := tail.push (bits >>> (8 * (7 - i))).toUInt8
  for i in [0:tail.size / 64] do
    state := compress state tail (64 * i)
  let mut out := ByteArray.emptyWithCapacity 32
  for word in state do
    for i in [0:4] do
      out := out.push (word >>> (8 * (3 - i)).toUInt32).toUInt8
  return out

private def hexDigit (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)

/-- The SHA-256 digest of `data` as 64 lowercase hexadecimal digits. -/
def hex (data : ByteArray) : String :=
  (digest data).foldl (init := "") fun s b => (s.push (hexDigit (b >>> 4))).push (hexDigit (b &&& 15))

/-- The SHA-256 digest of a text's UTF-8 bytes, in hexadecimal. -/
def hexOfString (text : String) : String :=
  hex text.toUTF8

end Informal.Sha256
