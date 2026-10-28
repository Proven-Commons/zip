# zip: a ZIP reader that cannot place a file outside its destination

This repo reads a ZIP archive and extracts its files into an in-memory list of paths and file contents. Every path it emits is built by joining the destination with a cleaned relative path. A machine-checked proof shows the cleaned path can never climb out of the destination.

It is a Proven Commons project, built to the verified bar published in the org's home repo, [mission](https://github.com/Proven-Commons/mission). Status: second slice, October 2026. Stored entries (method 0) and deflated entries (method 8, RFC 1951) are read. The full spec is in `SPEC.md`.

## Run it

Needs Lean 4.35.0 (install with elan, toolchain pinned in `lean-toolchain`).

```
lake build
.lake/build/bin/zip-pilot list <file.zip>
.lake/build/bin/zip-pilot manifest <file.zip> out
```

`list` prints one line per entry: name, size, and `file` or `dir`. `manifest` prints what extraction would do, in archive order, and writes nothing to disk: `OK` with the final path, size, and byte sum for an extracted file, `REJECT` for a file whose name fails the path gate, `SKIP` for a directory entry.

## What is proved

The path gate and the extraction rule, in `ZipPilot/Path.lean` and `ZipPilot/Archive.lean`:

- `gate_sound`: a name that passes the gate gives relative components with no `..`, no empty component, no `.`, and the list is not empty.
- `cleanComponents_sound`: the component cleaner behind the gate has the same properties.
- `extractAll_safe`: every path the extractor emits is the destination components followed by a gated relative path, so no emitted path escapes the destination.
- `extractArchive_safe`: the same guarantee for an archive read from bytes.

The gate rules: absolute names are rejected. Any `..` component is rejected. Empty and `.` components are dropped. A name with nothing left is rejected. Directory entries (names ending in `/`) are never extracted, so a directory entry cannot place a later entry outside the destination.

The deflate round trips, in `ZipPilot/Inflate.lean` and `ZipPilot/InflateProofs.lean`:

- `inflate_deflateStored`: inflating the stored-block writer's output returns the input bytes, for every input, whenever the cap (the declared uncompressed size) allows the input.
- `inflate_deflateFixed`: inflating the fixed Huffman writer's output returns the input bytes, for every input, whenever the cap allows the input. The proof inverts the fixed canonical code table symbol by symbol; how that works, and why the Huffman table builder had to change shape to make it possible, is written up at the end of `ZipPilot/InflateProofs.lean`.

The four gate and extraction theorems are unchanged from the first slice and cover entries read by either method: extraction still only writes bytes the gate passed.

Axiom check: each proof depends only on the standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`, or a subset). Full output is recorded in `tests/TEST-RESULTS.md`.

## How an archive is read

The end of central directory record is found first, by its signature and a comment that ends at the last byte of the file. The central directory it points at must end where that record begins. Each entry is then read through its local file header, which must agree with the central directory on the name, the flags, the method, the CRC-32, and both sizes. The entry bytes must end before the central directory starts. A stored entry's bytes are its contents. A deflated entry's bytes are a raw DEFLATE stream, decompressed with the declared uncompressed size as a cap. Either way, the resulting bytes must match the directory's size and CRC-32. A damaged entry turns the whole archive away.

An archive is also turned away when any entry uses a compression method other than 0 or 8, carries the encryption flag or the data descriptor flag, sits on another disk, or uses ZIP64 markers: a size or offset field of all ones, a ZIP64 extra field, or a ZIP64 end record or locator. Turning an archive away means an error and exit code 1, never a partial read.

## What is not proved

Read this before trusting the reader with real archives:

- Header parsing, the end record search, CRC-32, and archive reading are tested, not proved. The tests compare the Lean code against Python's `zipfile` module and against an independent copy of the extraction spec. Results are in `tests/TEST-RESULTS.md`: 4,488 checks, 0 failures, over 1,205 archive inputs (seed 20261025), covering normal files, hostile names, names that clean to nothing, random archives, broken inputs (truncated, garbage, wrong CRC, wrong entry count), deflated archives at four compression levels, and a raw deflate stream differential against Python's `zlib`.
- Inflate correctness beyond the two writer round trips (stored blocks and the fixed Huffman literal writer) rests on the differential tests, not on proof. In particular the dynamic Huffman table case has no proof: streams that use dynamic tables, back references, or the fixed distance code are covered by tests only. Fixed and dynamic blocks are covered by tests: zlib streams at levels 0, 1, 6, 9 with the default, fixed, RLE, and filtered strategies, and 500 mutated streams, all agreeing with Python zlib.
- Only methods 0 and 8 are read. Every other compression method turns the archive away.
- ZIP64 archives are turned away, not read. So are encrypted entries and streamed archives (entries with a data descriptor).
- Extraction works on an in-memory model. Nothing here writes files to disk, so the step from a proved in-memory path to a safe write on a real filesystem (races, symlinked destination folders) is outside this project for now.
- Names are read as UTF-8, as writers that set the UTF-8 flag write them. A name that is not valid UTF-8 reads as empty and is rejected by the gate. The CP437 reading for names without the UTF-8 flag is not implemented.
- ZIP names use `/` as the separator. A backslash inside a name is an ordinary character here, not a separator. Whether the gate should turn away backslashes is an open question in the plan issue for this repo.
- There is no ZIP writer. The only writers are the small deflate writers in `ZipPilot/Inflate.lean`, used for tests and the round trip proof: one emits stored blocks, the other fixed Huffman literal-only blocks.
- The Lean compiler, runtime, and kernel are trusted, as in every Lean project. A bug in them is outside the proof.

## Re-check it

```
lake build
lake env lean ZipPilot/Verify.lean
python3 tests/run_tests.py
```

The build fails if a proof breaks. The second command prints the axiom list. The test script rebuilds if needed, reruns every comparison, and rewrites `tests/TEST-RESULTS.md`.

## Layout

- `ZipPilot/Path.lean`: the path gate and its proofs.
- `ZipPilot/Header.lean`: the end of central directory record, the central directory, and extra field checks.
- `ZipPilot/Crc32.lean`: CRC-32, as used by the entry checksum check.
- `ZipPilot/Archive.lean`: whole-archive parse, local header checks, extraction, and the safety theorems.
- `ZipPilot/Inflate.lean`: the DEFLATE reader (RFC 1951) and the small deflate writers used by the tests and proofs.
- `ZipPilot/InflateProofs.lean`: the bit lemmas and the stored round trip proof.
- `ZipPilot/Verify.lean`: the axiom check.
- `Main.lean`: the command line front end.
- `SPEC.md`: the spec: what the reader accepts, the inflate rules, and what is and is not proved.
- `tests/run_tests.py`: differential tests against Python's `zipfile` and `zlib`.
