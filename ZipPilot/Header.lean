/-
  ZIP record layout: local file headers, central directory headers,
  and the end of central directory record.

  All integers are little endian. A local file header is 30 bytes:
  signature (4), version needed (2), flags (2), method (2), time (2),
  date (2), CRC-32 (4), compressed size (4), plain size (4), name
  length (2), extra length (2), then the name and the extra field,
  then the entry data.

  A central directory header is 46 bytes: signature (4), version made
  by (2), version needed (2), flags (2), method (2), time (2),
  date (2), CRC-32 (4), compressed size (4), plain size (4), name
  length (2), extra length (2), comment length (2), first disk (2),
  internal attributes (2), external attributes (4), local header
  offset (4), then the name, the extra field, and the comment.

  The end of central directory record is 22 bytes: signature (4),
  this disk (2), disk holding the directory start (2), entries on
  this disk (2), total entries (2), directory size (4), directory
  offset (4), comment length (2), then the comment.

  The reader reads stored entries (method 0) and deflated entries
  (method 8, see `Inflate.lean`). Parsing turns an archive away when
  any entry uses another method, carries the encryption flag or the
  data descriptor flag, sits on another disk, or uses ZIP64 markers
  (a size or offset field of all ones, or a ZIP64 extra field).
  Turning an archive away is an error, never a partial read.

  This code is covered by the differential tests in `tests/`, not by
  a proof. The proved part of this project is the path gate in
  `Path.lean` and the extraction rule in `Archive.lean`.
-/

namespace ZipPilot

/-- Byte at index `i`, or 0 when out of range. -/
def byteAt (b : ByteArray) (i : Nat) : UInt8 :=
  (b[i]?).getD 0

/-- The bytes of `b` in `[off, off + len)`, clamped to the array. -/
def sliceList (b : ByteArray) (off len : Nat) : List UInt8 :=
  (b.extract off (off + len)).toList

/-- A name field of `len` bytes at `off`, read as UTF-8.
    Invalid UTF-8 reads as the empty string. -/
def bytesToName (bs : List UInt8) : String :=
  (String.fromUTF8? (ByteArray.mk bs.toArray)).getD ""

/-- A two byte little endian number at `off`. -/
def u16 (b : ByteArray) (off : Nat) : Nat :=
  (byteAt b off).toNat + 256 * (byteAt b (off + 1)).toNat

/-- A four byte little endian number at `off`. -/
def u32 (b : ByteArray) (off : Nat) : Nat :=
  (byteAt b off).toNat + 256 * (byteAt b (off + 1)).toNat +
    65536 * (byteAt b (off + 2)).toNat + 16777216 * (byteAt b (off + 3)).toNat

/-- Scan an extra field for a ZIP64 entry (header id 0x0001).
    The first argument is fuel: each step eats at least four bytes,
    so the field length bounds the steps. A field that does not parse
    gives `none`. -/
def scanExtra (data : ByteArray) : Nat → Nat → Nat → Option Bool
  | _, _, 0 => some false
  | 0, _, _ => none
  | fuel + 1, off, rem =>
    if rem < 4 then none
    else
      let id := u16 data off
      let sz := u16 data (off + 2)
      if sz + 4 > rem then none
      else if id = 0x0001 then some true
      else scanExtra data fuel (off + 4 + sz) (rem - 4 - sz)

/-- True when an extra field holds a ZIP64 entry, false when it does
    not, and `none` when the field does not parse. -/
def extraHasZip64 (data : ByteArray) (off len : Nat) : Option Bool :=
  scanExtra data len off len

/-- What the end of central directory record tells us, after checks. -/
structure Eocd where
  cdOffset : Nat
  cdSize : Nat
  count : Nat
  deriving Repr

/-- True when a 22 byte end record sits at `i`: signature matches and
    its comment ends at the last byte of the file. -/
def eocdAt (data : ByteArray) (i : Nat) : Bool :=
  u32 data i = 0x06054b50 && i + 22 + u16 data (i + 20) = data.size

/-- Find the end of central directory record. The last position in the
    file whose comment ends at the last byte is the record. -/
def findEocd (data : ByteArray) : Option Nat :=
  ((List.range (data.size + 1 - 22)).filter (fun i => eocdAt data i)).getLast?

/-- Read the end record at `pos`. Multi-disk archives and archives
    with ZIP64 sentinel values in the size, offset, or count fields
    are turned away. -/
def parseEocd (data : ByteArray) (pos : Nat) : Option Eocd :=
  let disk := u16 data (pos + 4)
  let cdDisk := u16 data (pos + 6)
  let nDisk := u16 data (pos + 8)
  let nTot := u16 data (pos + 10)
  let cdSize := u32 data (pos + 12)
  let cdOff := u32 data (pos + 16)
  if disk ≠ 0 ∨ cdDisk ≠ 0 ∨ nDisk ≠ nTot then none
  else if nTot = 0xFFFF ∨ cdSize = 0xFFFFFFFF ∨ cdOff = 0xFFFFFFFF then none
  else if cdOff + cdSize ≠ pos then none
  else some { cdOffset := cdOff, cdSize := cdSize, count := nTot }

/-- One central directory entry, with the fields this reader uses. -/
structure CentralEntry where
  name : String
  flags : Nat
  method : Nat
  crc : Nat
  compSize : Nat
  size : Nat
  localOffset : Nat
  deriving Repr

/-- Parse and check one central directory header at `off`.
    Returns the entry and the offset just past it. -/
def parseCentralHeader (data : ByteArray) (off : Nat) : Option (CentralEntry × Nat) :=
  if off + 46 > data.size then none
  else if u32 data off ≠ 0x02014b50 then none
  else
    let flags := u16 data (off + 8)
    let method := u16 data (off + 10)
    let crc := u32 data (off + 16)
    let comp := u32 data (off + 20)
    let size := u32 data (off + 24)
    let nLen := u16 data (off + 28)
    let xLen := u16 data (off + 30)
    let cLen := u16 data (off + 32)
    let disk := u16 data (off + 34)
    let localOff := u32 data (off + 42)
    let total := 46 + nLen + xLen + cLen
    if flags % 2 = 1 ∨ (flags / 8) % 2 = 1 then none
    else if method ≠ 0 ∧ method ≠ 8 then none
    else if disk ≠ 0 then none
    else if comp = 0xFFFFFFFF ∨ size = 0xFFFFFFFF ∨ localOff = 0xFFFFFFFF then none
    else if off + total > data.size then none
    else match extraHasZip64 data (off + 46 + nLen) xLen with
      | none => none
      | some true => none
      | some false =>
        some ({ name := bytesToName (sliceList data (off + 46) nLen),
                flags := flags, method := method, crc := crc,
                compSize := comp, size := size, localOffset := localOff },
              off + total)

/-- Parse `count` central directory headers starting at `off`.
    The first argument after the data is fuel, counted down once per
    header, so the count from the end record bounds the loop.
    Returns the entries and the offset just past the last header. -/
def parseCentral (data : ByteArray) : Nat → Nat → Option (List CentralEntry × Nat)
  | 0, off => some ([], off)
  | fuel + 1, off => do
    let (e, next) ← parseCentralHeader data off
    let (rest, fin) ← parseCentral data fuel next
    return (e :: rest, fin)

end ZipPilot
