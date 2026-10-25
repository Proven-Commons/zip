/-
  CRC-32, the checksum stored in every ZIP entry header, computed a
  byte at a time from a table. The parser checks each stored entry
  against the CRC in its headers, so a corrupted entry is rejected
  instead of being handed out with wrong bytes.

  The code follows the codec pack's CRC-32 in Proven-Commons/codec.
  It is covered by the differential tests in `tests/`, not by a proof.
-/

namespace ZipPilot.Crc32

/-- One step of the shift register: shift toward the low end, and xor in
    the reflected polynomial 0xEDB88320 when a one bit falls out. -/
def step (c : UInt32) : UInt32 :=
  if c &&& 1 = 1 then (c >>> 1) ^^^ 0xEDB88320 else c >>> 1

/-- Eight steps: one byte's worth. -/
def step8 (c : UInt32) : UInt32 :=
  step (step (step (step (step (step (step (step c)))))))

/-- `table[i]` is eight steps from `i`. -/
def table : Array UInt32 :=
  (Array.range 256).map fun i => step8 i.toUInt32

/-- Feed one byte into the register. -/
def update (c : UInt32) (b : UInt8) : UInt32 :=
  table[((c ^^^ b.toUInt32) &&& 0xFF).toNat]! ^^^ (c >>> 8)

/-- The CRC-32 of a message. -/
def crc32 (bs : List UInt8) : UInt32 :=
  bs.foldl update 0xFFFFFFFF ^^^ 0xFFFFFFFF

end ZipPilot.Crc32
