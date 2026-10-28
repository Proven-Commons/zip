# Specification: the Proven Commons ZIP reader

This file states exactly what the reader accepts, what it does with
what it accepts, and what it turns away. The code in `ZipPilot/`
implements this spec. The proofs cover part of it; the rest is
covered by the differential tests in `tests/`.

## Command line protocol

Two commands, run as `zip-pilot <command> ...`:

- `zip-pilot list <file.zip>` prints one line per entry, in archive
  order: the entry name, a tab, the uncompressed size, a tab, and
  `file` or `dir`.
- `zip-pilot manifest <file.zip> <dest>` prints what extraction
  would do, in archive order, and writes nothing to disk. One line
  per entry:
  - `OK`, a tab, the final path (the destination joined with the
    cleaned relative path), a tab, the size, a tab, the byte sum of
    the contents, for a file that passes the path gate.
  - `REJECT`, a tab, the entry name, for a file whose name fails
    the path gate.
  - `SKIP`, a tab, the entry name, a tab, `directory`, for a
    directory entry.

An archive that is turned away (see the rejection list) prints an
error to stderr and exits with code 1, for both commands. A read
archive exits with code 0. This protocol is unchanged from the
first slice: deflated entries now list and verify instead of
turning the archive away.

## How an archive is read

The end of central directory record is found first, by its
signature and a comment that ends at the last byte of the file.
The central directory it points at must end where that record
begins. Each entry is read through its local file header, which
must agree with the central directory on the name, the flags, the
method, the CRC-32, and both sizes. The entry data must end before
the central directory starts.

Entry data is read by method:

- Method 0 (stored): the bytes are the contents, as they are.
- Method 8 (deflate): the bytes are a raw DEFLATE stream (RFC
  1951), decompressed by the inflate rules below.
- Every other method turns the archive away.

A deflated entry faces two size caps before any inflation work
starts, both read from the header sizes alone. The declared
uncompressed size may be at most 256 MiB (268435456 bytes): the
size fields are four bytes wide, so without a fixed cap an entry
could claim up to 4 GiB of output and have the reader try to
produce it, and 256 MiB sits far above the entries this reader
is aimed at. The declared uncompressed size may also be at most
1000 times the compressed size: a real deflate stream cannot do
much better than about 1032 to 1, so the ratio cap refuses
almost nothing honest, and it stops an entry that spends a small
archive on a much larger output even when that output stays
under the size cap. Going past either cap turns the archive
away.

Whichever method was used, the bytes then face two checks: their
length must equal the uncompressed size in the directory, and
their CRC-32 must match the directory. A failure anywhere turns
the whole archive away. There is never a partial read.

## The path gate

Extraction only emits a path built from the destination and a
cleaned relative path. The cleaning rules:

- Absolute names are rejected.
- Any `..` component is rejected.
- Empty and `.` components are dropped.
- A name with nothing left after cleaning is rejected.
- Directory entries (names ending in `/`) are never extracted.

Names are read as UTF-8. A name that is not valid UTF-8 reads as
empty and is rejected by the gate. The CP437 reading for names
without the UTF-8 flag is not implemented. ZIP names use `/` as
the separator; a backslash inside a name is an ordinary character
here, not a separator. Whether the gate should turn away
backslashes is still an open question.

## Rejection list

An archive is turned away when any of these holds:

- The file is empty, is not a ZIP archive, or is truncated.
- The end record, the central directory, or a local header is
  malformed, disagrees with another part, or runs past the end of
  the file.
- An entry uses a method other than 0 or 8.
- A deflated entry declares an uncompressed size over 256 MiB,
  or an uncompressed size more than 1000 times its compressed
  size.
- An entry carries the encryption flag or the data descriptor
  flag. (A data descriptor means the archive was streamed; streamed
  archives are outside this reader.)
- An entry sits on another disk.
- ZIP64 markers appear: a size or offset field of all ones, a
  ZIP64 extra field, or a ZIP64 end record or locator.
- An entry's stored bytes fail the size or CRC-32 check.
- A deflate stream breaks any inflate rule below.

## Inflate rules (RFC 1951)

Input: a raw DEFLATE stream (no zlib or gzip wrapper) and a cap,
the declared uncompressed size. Output: the decompressed bytes, or
an error.

- Bits are read least significant bit first, as the RFC states.
- Blocks are read until one marked final (BFINAL). Running out of
  input before a final block, or a stream that ends mid block, is
  an error.
- Block type (BTYPE): 00 stored, 01 fixed Huffman, 10 dynamic
  Huffman, 11 is reserved and is an error.
- Stored: skip to the next byte boundary, read LEN and NLEN; they
  must agree (LEN + NLEN = 65535); copy LEN bytes.
- Huffman codes are canonical codes built from code lengths, as
  the RFC describes. Decoding walks the code one bit at a time.
- The literal and length alphabet has 288 symbols. Symbols 0 to
  255 are bytes, 256 ends the block, 257 to 285 are length codes
  with the RFC's base lengths and extra bits. Symbol 286 or above
  appearing in a stream is an error.
- The distance alphabet has 30 codes (0 to 29) with the RFC's base
  distances and extra bits. Distance symbols 30 and 31 appearing
  in a stream are an error. A copy reads a length and a distance
  and copies from the output so far; overlapping copies are
  allowed. A distance of zero, or one that reaches before the
  start of the output, is an error.
- Dynamic header: HLIT (literal codes, 257 plus the field),
  HDIST (distance codes, 1 plus the field), HCLEN, then the code
  length code lengths in the RFC's order (16, 17, 18, 0, 8, 7, 9,
  6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15), then the literal and
  distance lengths read with that code, including the repeat codes
  16 (repeat the previous length, 3 to 6 times), 17 (zeros, 3 to
  10), and 18 (zeros, 11 to 138). Reading past the declared number
  of lengths is an error, as is a repeat with no length before it.
- HLIT above 286 or HDIST above 30 is an error. A literal table
  with no length for symbol 256 (end of block) is an error.
- Code validity: a Huffman code built from lengths must be
  complete (the Kraft sum is exactly full), with the RFC's
  exceptions: a code with a single symbol of length 1 is allowed,
  an empty distance code (all lengths zero) is allowed until a
  distance is actually read from it, and the fixed tables are used
  as the RFC gives them. Over-subscribed or otherwise incomplete
  codes are errors.
- The output may not grow past the cap. Running past it is an
  error. Bits or bytes left over after the final block are
  ignored; the size and CRC-32 checks outside inflate catch any
  harm they could hide.

## What is proved

Machine-checked in Lean, depending only on the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`, or a subset):

- `gate_sound`, `cleanComponents_sound`: a name that passes the
  gate gives relative components with no `..`, no empty component,
  no `.`, and the list is not empty.
- `extractAll_safe`, `extractArchive_safe`: every path the
  extractor emits is the destination followed by a gated relative
  path, for entries read by either method. Extraction still only
  writes bytes the gate passed.
- `inflate_deflateStored`: inflating the stored-block writer's
  output returns the input bytes, for every input, whenever the
  cap allows the input. The writer is the small one in
  `ZipPilot/Inflate.lean` that emits stored blocks.
- `inflate_deflateFixed`: inflating the fixed Huffman writer's
  output returns the input bytes, for every input, whenever the
  cap allows the input. The writer is the other small one in
  `ZipPilot/Inflate.lean`, which emits one fixed Huffman block of
  literal bytes only. The proof inverts the fixed canonical code
  table symbol by symbol.

## What is not proved

- Inflate correctness beyond the two writer round trips (stored
  blocks and the fixed Huffman literal writer) rests on the
  differential tests, not on proof. In particular the dynamic
  Huffman table case has no proof, and neither do streams using
  back references or the fixed distance code. Fixed and dynamic
  blocks are covered by the tests in `tests/TEST-RESULTS.md`
  (zlib streams at levels 0, 1, 6, 9 with four strategies,
  zipfile archives, and 500 mutated streams, all agreeing with
  Python zlib).
- Header parsing, the end record search, and CRC-32 are tested,
  not proved.
- ZIP64, encryption, and streamed archives (data descriptors) are
  turned away, not read.
- There is no general ZIP writer. The only writers are the small
  deflate writers used for tests and the round trip proof (stored
  blocks, and fixed Huffman literal-only blocks).
- Extraction works on an in-memory model. The step from a proved
  in-memory path to a safe write on a real filesystem (races,
  symlinked destination folders) is outside this project for now.

## What you must trust

- The Lean compiler, runtime, and kernel, as in every Lean
  project.
- The test oracle for everything not proved: Python's `zipfile`
  and `zlib`, and the independent copy of the extraction spec in
  `tests/run_tests.py`.

## Re-check it

```
lake build
lake env lean ZipPilot/Verify.lean
python3 tests/run_tests.py
```

The build fails if a proof breaks. The second command prints the
axiom list for the six theorems. The test script rebuilds if
needed, reruns every comparison, and rewrites
`tests/TEST-RESULTS.md`.
