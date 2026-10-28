/-
  DEFLATE decompression (RFC 1951), the second slice of this reader.

  `inflate` turns a raw DEFLATE stream (the compressed bytes of a
  method 8 entry) back into the plain bytes. The work is done on a
  list of bits, least significant bit first inside each byte, as the
  RFC packs bits. The declared plain size from the central directory
  is a cap: output that would run past the cap is an error, as are a
  stream that ends early, a stream that ends without a final block,
  a wrong stored length check, an over-subscribed or (with narrow
  exceptions below) incomplete Huffman code, a distance symbol of
  30 or 31, a length symbol of 286 or 287, and a copy distance that
  reaches back before the start of the output.

  The Huffman table rules follow the reference decoder, checked
  against Python's `zlib` on hand-built streams: a code must be
  complete (its Kraft sum fills the space) or have a single symbol
  of length 1. The distance code alone may also be empty (no symbol
  used); reading a distance from an empty code is an error. The
  fixed tables are used as the RFC gives them: the fixed distance
  code has 32 symbols of length 5, and its Kraft sum is complete
  (32 codes of length 5 fill the space exactly). Only symbols 30
  and 31 are unused, since the distance alphabet stops at 29; the
  decoder turns those two away when they appear.

  Also here: a small DEFLATE writer, `deflateStored` and
  `deflateFixed`. The writer exists for tests and for the round trip
  proof in `InflateProofs.lean`. It writes stored blocks, or one
  fixed Huffman block holding literal bytes only (no back
  references).

  Correctness of `inflate` beyond the writer round trips rests on
  the differential tests in `tests/`, not on a proof.
-/

namespace ZipPilot

/-! ## Bits -/

/-- `n` bits of `v`, least significant bit first. -/
def bitsOfNat : Nat → Nat → List Bool
  | 0, _ => []
  | n + 1, v => (v % 2 = 1) :: bitsOfNat n (v / 2)

/-- The value of a bit list, least significant bit first. -/
def valOfBits : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * valOfBits bs

/-- The bits of one byte, least significant bit first. -/
def byteBits (b : UInt8) : List Bool :=
  bitsOfNat 8 b.toNat

/-- The bits of a byte string, in stream order. -/
def bytesToBits (bs : List UInt8) : List Bool :=
  bs.flatMap byteBits

/-- The byte whose bits are the given list (read past the end of the
    list as zero bits). -/
def bitsToByte (bs : List Bool) : UInt8 :=
  (valOfBits bs).toUInt8

/-! ## The bit reader -/

/-- A position in a bit stream: the bits still to read, how many
    of them remain, and how many bits have been read so far. The
    remaining count is carried in the state so that no reader has
    to measure the bit list to know whether a read fits: measuring
    it on every read made inflation roughly quadratic in the
    stream size. Every step that consumes bits drops the count by
    the same amount, so the count always equals the length of the
    remaining list. The read count is what stored blocks align on:
    a stored block's data starts on a byte boundary of the whole
    stream. -/
structure BR where
  rest : List Bool
  rem : Nat
  pos : Nat

/-- Read `n` bits as a value, least significant bit first.
    Fails when fewer than `n` bits remain. -/
def readBits (n : Nat) : BR → Option (Nat × BR)
  | ⟨rest, rem, pos⟩ =>
    if rem < n then none
    else some (valOfBits (rest.take n), ⟨rest.drop n, rem - n, pos + n⟩)

/-- Skip forward to the next byte boundary of the stream. -/
def alignByte : BR → BR
  | ⟨rest, rem, pos⟩ =>
    let d := (8 - pos % 8) % 8
    ⟨rest.drop d, rem - d, pos + d⟩

/-- Read `n` whole bytes' worth of bits (in whatever position the
    stream is in) and give them back as bytes, sharing work with
    the tail of the stream. -/
def readBytesAux : Nat → List Bool → List UInt8 × List Bool
  | 0, bits => ([], bits)
  | n + 1, bits =>
    let (bs, rest) := readBytesAux n (bits.drop 8)
    (bitsToByte (bits.take 8) :: bs, rest)

/-- Read `n` bytes. Fails when fewer than `8 * n` bits remain. -/
def readBytes (n : Nat) : BR → Option (List UInt8 × BR)
  | ⟨rest, rem, pos⟩ =>
    if rem < 8 * n then none
    else
      let (bs, rest') := readBytesAux n rest
      some (bs, ⟨rest', rem - 8 * n, pos + 8 * n⟩)

/-! ## Huffman codes -/

/-- A canonical Huffman code in decoding form. `counts[l]` is the
    number of symbols whose code has length `l`, `firstCode[l]` the
    first code of that length, `firstIdx[l]` the position in `syms`
    of the first symbol of that length. `syms` lists the symbols
    with a code, sorted by code length and then by symbol, which is
    the order canonical codes are handed out in. -/
structure Huff where
  maxLen : Nat
  counts : Array Nat
  firstCode : Array Nat
  firstIdx : Array Nat
  syms : Array Nat

/-- First code of each length, from the counts per length. The
    count of length 0 is forced to 0 by the caller, as the RFC's
    algorithm states. -/
def firstCodes : List Nat → List Nat :=
  go 0
where
  go (code : Nat) : List Nat → List Nat
    | [] => []
    | c :: cs => code :: go ((code + c) * 2) cs

/-- Build the decoding table for a list of code lengths, one per
    symbol. Symbols with length 0 have no code. -/
def buildHuff (lengths : List Nat) : Huff :=
  let maxLen := lengths.foldl Nat.max 0
  let counts := (List.range (maxLen + 1)).map fun l =>
    if l = 0 then 0 else (lengths.filter (· = l)).length
  let pairs := (lengths.zipIdx).filterMap fun (l, s) =>
    if l > 0 then some (l, s) else none
  -- The symbols in canonical order: by code length, then by symbol.
  -- Grouping by length gives that order directly, since `pairs` is
  -- already in symbol order. (This construction replaced a merge
  -- sort of the pairs: the result is the same list, because the
  -- order is total on pairs, but this one is plain structural
  -- recursion, so proofs can compute with it; the sort could not
  -- be unfolded by the kernel at all.)
  let sorted := ((List.range maxLen).map (· + 1)).flatMap fun l =>
    pairs.filter fun p => p.1 = l
  let firstIdx := (List.range (maxLen + 1)).map fun l =>
    (counts.take l).foldl (· + ·) 0
  { maxLen := maxLen,
    counts := counts.toArray,
    firstCode := (firstCodes counts).toArray,
    firstIdx := firstIdx.toArray,
    syms := (sorted.map Prod.snd).toArray }

/-- The Kraft sum of a length list, scaled by `2 ^ maxLen`: the sum
    of `2 ^ (maxLen - l)` over symbols with a code. A complete code
    has this equal to `2 ^ maxLen`. -/
def kraftSum (lengths : List Nat) : Nat :=
  let m := lengths.foldl Nat.max 0
  lengths.foldl (fun acc l => if l = 0 then acc else acc + 2 ^ (m - l)) 0

/-- Whether a length list may be used as a Huffman code. It must be
    complete, or have a single symbol of length 1. An empty list of
    lengths (no symbol used) passes only when `allowEmpty` is set,
    which the reader sets for the distance code alone, following the
    reference decoder. -/
def tableValid (lengths : List Nat) (allowEmpty : Bool) : Bool :=
  let used := lengths.filter (· > 0)
  if used.isEmpty then allowEmpty
  else
    let m := lengths.foldl Nat.max 0
    kraftSum lengths = 2 ^ m || (used.length = 1 && (used.head?.getD 0) = 1)

/-- Decode one Huffman symbol. Walks the stream bit by bit, most
    significant code bit first, and stops at the length whose code
    range holds the bits read so far. -/
def huffDecode (h : Huff) (r : BR) : Option (Nat × BR) :=
  go h.maxLen 0 0 r
where
  go : Nat → Nat → Nat → BR → Option (Nat × BR)
    | 0, _, _, _ => none
    | fuel + 1, code, len, r =>
      match r.rest with
      | [] => none
      | b :: rest =>
        let code' := code * 2 + (if b then 1 else 0)
        let len' := len + 1
        let fc := (h.firstCode[len']?).getD 0
        let cnt := (h.counts[len']?).getD 0
        if fc ≤ code' && code' - fc < cnt then
          some ((h.syms[(h.firstIdx[len']?).getD 0 + (code' - fc)]?).getD 0,
            ⟨rest, r.rem - 1, r.pos + 1⟩)
        else go fuel code' len' ⟨rest, r.rem - 1, r.pos + 1⟩

/-! ## The block data -/

/-- Base lengths for length symbols 257 to 285 (RFC 1951 3.2.5). -/
def lenBase : List Nat :=
  [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43,
   51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258]

/-- Extra bit counts for length symbols 257 to 285. -/
def lenExtra : List Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4,
   4, 4, 5, 5, 5, 5, 0]

/-- Base distances for distance symbols 0 to 29. -/
def distBase : List Nat :=
  [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257,
   385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289,
   16385, 24577]

/-- Extra bit counts for distance symbols 0 to 29. -/
def distExtra : List Nat :=
  [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9,
   10, 10, 11, 11, 12, 12, 13, 13]

/-- Copy `len` bytes from `dist` bytes back in the output, one byte
    at a time, so a copy may overlap its own source. A distance of
    zero, or one that reaches before the start of the output, is an
    error. The caller has already turned such distances away, so
    this check is a second line of defence. -/
def copyBytes (out : Array UInt8) (dist len : Nat) : Option (Array UInt8) :=
  go len out
where
  go : Nat → Array UInt8 → Option (Array UInt8)
    | 0, o => some o
    | n + 1, o =>
      if dist = 0 || dist > o.size then none
      else go n (o.push ((o[o.size - dist]?).getD 0))

/-- Read the data of one compressed block: symbols until the end of
    block symbol (256). The output may not grow past `cap`. The
    first argument is fuel: every symbol takes at least one bit, so
    the bits left in the stream bound the loop. -/
def decodeSymbols : Nat → Huff → Huff → BR → Array UInt8 → Nat →
    Option (Array UInt8 × BR)
  | 0, _, _, _, _, _ => none
  | fuel + 1, lit, dist, r, out, cap =>
    (huffDecode lit r).bind fun (sym, r) =>
    if sym < 256 then
      let out := out.push sym.toUInt8
      if cap < out.size then none
      else decodeSymbols fuel lit dist r out cap
    else if sym = 256 then
      some (out, r)
    else if sym ≤ 285 then
      let li := sym - 257
      (readBits (lenExtra.getD li 0) r).bind fun (extra, r) =>
      let length := lenBase.getD li 0 + extra
      (huffDecode dist r).bind fun (dsym, r) =>
      if 30 ≤ dsym then none
      else
        (readBits (distExtra.getD dsym 0) r).bind fun (dextra, r) =>
        let d := distBase.getD dsym 0 + dextra
        if out.size < d then none
        else
          (copyBytes out d length).bind fun out =>
          if cap < out.size then none
          else decodeSymbols fuel lit dist r out cap
    else none

/-! ## The dynamic table header -/

/-- The order the code length code's lengths are sent in. -/
def clOrder : List Nat :=
  [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

/-- Read `count` values of `k` bits each. -/
def readVals : Nat → Nat → BR → Option (List Nat × BR)
  | _, 0, r => some ([], r)
  | k, n + 1, r =>
    (readBits k r).bind fun (v, r) =>
    (readVals k n r).bind fun (vs, r) =>
    some (v :: vs, r)

/-- Read the code length code: `n` lengths of 3 bits in the RFC's
    order, the remaining lengths zero. Returns all 19 lengths, by
    symbol. -/
def readCL (n : Nat) (r : BR) : Option (List Nat × BR) :=
  (readVals 3 n r).bind fun (vals, r) =>
  let lens := (List.range 19).map fun s =>
    match clOrder.zipIdx.find? (fun (sym, _) => sym = s) with
    | some (_, p) => vals.getD p 0
    | none => 0
  some (lens, r)

/-- Read `total` code lengths with the code length code, expanding
    the repeat symbols 16 (repeat the last length, 3 to 6 times),
    17 (zeros, 3 to 10 times), and 18 (zeros, 11 to 138 times).
    Running past `total` is an error, as is a repeat with no length
    before it. Fuel: every step reads at least one Huffman symbol,
    hence at least one bit, so the bits left bound the loop. -/
def readLens (cl : Huff) (total : Nat) (r : BR) : Option (List Nat × BR) :=
  go (r.rem + total + 1) r []
where
  go : Nat → BR → List Nat → Option (List Nat × BR)
    | 0, _, _ => none
    | fuel + 1, r, acc =>
      if acc.length = total then some (acc, r)
      else
        (huffDecode cl r).bind fun (sym, r) =>
        if sym < 16 then
          if total < acc.length + 1 then none
          else go fuel r (acc ++ [sym])
        else if sym = 16 then
          match acc.getLast? with
          | none => none
          | some prev =>
            (readBits 2 r).bind fun (e, r) =>
            if total < acc.length + (e + 3) then none
            else go fuel r (acc ++ List.replicate (e + 3) prev)
        else if sym = 17 then
          (readBits 3 r).bind fun (e, r) =>
          if total < acc.length + (e + 3) then none
          else go fuel r (acc ++ List.replicate (e + 3) 0)
        else if sym = 18 then
          (readBits 7 r).bind fun (e, r) =>
          if total < acc.length + (e + 11) then none
          else go fuel r (acc ++ List.replicate (e + 11) 0)
        else none

/-- Read a dynamic block's tables: the counts, the code length
    code, then the literal and distance lengths. More than 286
    literal codes or 30 distance codes is an error, as is a missing
    end of block code. -/
def dynamicTables (r : BR) : Option (Huff × Huff × BR) :=
  (readBits 5 r).bind fun (hlitF, r) =>
  (readBits 5 r).bind fun (hdistF, r) =>
  (readBits 4 r).bind fun (hclenF, r) =>
  let hlit := hlitF + 257
  let hdist := hdistF + 1
  if 286 < hlit || 30 < hdist then none
  else
    (readCL (hclenF + 4) r).bind fun (clLens, r) =>
    if !tableValid clLens false then none
    else
      (readLens (buildHuff clLens) (hlit + hdist) r).bind fun (combined, r) =>
      let litLens := combined.take hlit
      let distLens := combined.drop hlit
      if (litLens[256]?).getD 0 = 0 then none
      else if !tableValid litLens false then none
      else if !tableValid distLens true then none
      else some (buildHuff litLens, buildHuff distLens, r)

/-! ## The fixed tables -/

/-- Code lengths of the fixed literal code (RFC 1951 3.2.6). -/
def fixedLitLengths : List Nat :=
  (List.range 288).map fun s =>
    if s < 144 then 8 else if s < 256 then 9 else if s < 280 then 7 else 8

/-- Code lengths of the fixed distance code: 32 codes of length 5,
    as the RFC gives them. The code is complete: 32 codes of
    length 5 fill the Kraft sum exactly. Only symbols 30 and 31
    are unused, since the distance alphabet stops at 29; the
    decoder turns those two away when they appear. -/
def fixedDistLengths : List Nat :=
  List.replicate 32 5

def fixedLitTable : Huff := buildHuff fixedLitLengths

def fixedDistTable : Huff := buildHuff fixedDistLengths

/-! ## Blocks and the whole stream -/

/-- Read blocks until one marked final. The output may not grow
    past `cap`. The first argument is fuel: every block takes at
    least three bits (its header), so the bits in the stream bound
    the loop. -/
def blocks : Nat → BR → Array UInt8 → Nat → Option (Array UInt8)
  | 0, _, _, _ => none
  | fuel + 1, r, out, cap =>
    (readBits 1 r).bind fun (bf, r) =>
    (readBits 2 r).bind fun (bt, r) =>
    if bt = 0 then
      (readBits 16 (alignByte r)).bind fun (len, r) =>
      (readBits 16 r).bind fun (nlen, r) =>
      if len + nlen ≠ 65535 then none
      else
        (readBytes len r).bind fun (bytes, r) =>
        let out := bytes.foldl Array.push out
        if cap < out.size then none
        else if bf = 1 then some out
        else blocks fuel r out cap
    else if bt = 1 then
      (decodeSymbols (r.rem + 1) fixedLitTable fixedDistTable r out
        cap).bind fun (out, r) =>
      if bf = 1 then some out
      else blocks fuel r out cap
    else if bt = 2 then
      (dynamicTables r).bind fun (lit, dist, r) =>
      (decodeSymbols (r.rem + 1) lit dist r out cap).bind fun (out, r) =>
      if bf = 1 then some out
      else blocks fuel r out cap
    else none

/-- Decompress a raw DEFLATE stream. `cap` is the declared plain
    size: output that would run past it is an error. Bits or bytes
    left over after the final block are ignored, as the reference
    decoders ignore them when a size and a checksum are checked
    outside, which the ZIP reader does. -/
def inflate (input : List UInt8) (cap : Nat) : Option (List UInt8) :=
  let bits := bytesToBits input
  (blocks (bits.length + 1) ⟨bits, bits.length, 0⟩ #[] cap).map Array.toList

/-! ## A small writer, for tests and proofs -/

/-- The bits of a Huffman code, most significant bit first, as codes
    are written to the stream. -/
def codeBits (code len : Nat) : List Bool :=
  (bitsOfNat len code).reverse

/-- The canonical code of symbol `s` in the code with the given
    lengths, and its length. -/
def canonCode (lengths : List Nat) (s : Nat) : Nat × Nat :=
  let l := lengths.getD s 0
  let maxLen := lengths.foldl Nat.max 0
  let counts := (List.range (maxLen + 1)).map fun k =>
    if k = 0 then 0 else (lengths.filter (· = k)).length
  let rank := ((lengths.take s).filter (· = l)).length
  ((firstCodes counts).getD l 0 + rank, l)

/-- One stored block as bytes: the header byte (the final flag in
    the low bit, the stored type above it, zeros up to the byte
    boundary), the length, its complement, and the bytes. The chunk
    must be at most 65535 bytes; `deflateStored` cuts its input so. -/
def storedBlockBytes (final : Bool) (chunk : List UInt8) : List UInt8 :=
  let len := chunk.length
  (if final then 1 else 0).toUInt8 ::
  (len % 256).toUInt8 :: (len / 256).toUInt8 ::
  ((65535 - len) % 256).toUInt8 :: ((65535 - len) / 256).toUInt8 :: chunk

/-- The bytes of a chain of stored blocks. All blocks but the last
    are marked not final. An empty chain still writes one empty
    final block, so the stream is never empty. -/
def storedChainBytes : List (List UInt8) → List UInt8
  | [] => storedBlockBytes true []
  | [c] => storedBlockBytes true c
  | c :: (c' :: cs) =>
    storedBlockBytes false c ++ storedChainBytes (c' :: cs)

/-- Cut a list into chunks of at most `n`. The second argument is
    fuel, the length of the input when called from `deflateStored`. -/
def chunksOf (n : Nat) : Nat → List UInt8 → List (List UInt8)
  | _, [] => []
  | 0, _ :: _ => []
  | fuel + 1, l => l.take n :: chunksOf n fuel (l.drop n)

/-- Compress by storing: a chain of stored blocks. -/
def deflateStored (data : List UInt8) : List UInt8 :=
  storedChainBytes (chunksOf 65535 data.length data)

/-- Pack bits into bytes, the last byte padded with zero bits. The
    first argument is fuel: the number of bits when called from
    `deflateFixed` is more than enough groups of eight. -/
def packAux : Nat → List Bool → List UInt8
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, bits => bitsToByte (bits.take 8) :: packAux n (bits.drop 8)

/-- Compress with the fixed Huffman code, literals only: one final
    block, each byte as its literal code, then the end of block
    code, padded to a whole byte. -/
def deflateFixed (data : List UInt8) : List UInt8 :=
  let bits : List Bool :=
    [true, true, false] ++
    (data.flatMap fun b =>
      let (c, l) := canonCode fixedLitLengths b.toNat
      codeBits c l) ++
    (let (c, l) := canonCode fixedLitLengths 256
     codeBits c l)
  let pad := (8 - bits.length % 8) % 8
  packAux bits.length (bits ++ List.replicate pad false)

end ZipPilot
