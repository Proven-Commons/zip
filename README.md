# zip: a ZIP reader that cannot place a file outside its destination

This repo reads a ZIP archive and extracts stored files into an in-memory list of paths and file contents. Every path it emits is built by joining the destination with a cleaned relative path. A machine-checked proof shows the cleaned path can never climb out of the destination.

It is a Proven Commons project, built to the verified bar published in the org's home repo, [mission](https://github.com/Proven-Commons/mission). Status: first slice, October 2026. Stored entries only (compression method 0).

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

Axiom check: each proof depends only on the standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`, or a subset). Full output is recorded in `tests/TEST-RESULTS.md`.

## How an archive is read

The end of central directory record is found first, by its signature and a comment that ends at the last byte of the file. The central directory it points at must end where that record begins. Each entry is then read through its local file header, which must agree with the central directory on the name, the flags, the method, the CRC-32, and both sizes. The stored bytes must end before the central directory starts, and their CRC-32 must match the headers. A damaged entry turns the whole archive away.

An archive is also turned away when any entry uses a compression method other than 0, carries the encryption flag or the data descriptor flag, sits on another disk, or uses ZIP64 markers: a size or offset field of all ones, a ZIP64 extra field, or a ZIP64 end record or locator. Turning an archive away means an error and exit code 1, never a partial read.

## What is not proved

Read this before trusting the reader with real archives:

- Header parsing, the end record search, CRC-32, and archive reading are tested, not proved. The tests compare the Lean code against Python's `zipfile` module and against an independent copy of the extraction spec. Results are in `tests/TEST-RESULTS.md`: 3,058 checks, 0 failures, over 620 archive inputs (seed 20261025), covering normal files, hostile names, names that clean to nothing, random archives, and broken inputs (truncated, garbage, wrong CRC, wrong entry count).
- Only stored entries (method 0) are read. Deflate and every other compression method are outside this slice and turn the archive away.
- ZIP64 archives are turned away, not read.
- Extraction works on an in-memory model. Nothing here writes files to disk, so the step from a proved in-memory path to a safe write on a real filesystem (races, symlinked destination folders) is outside this project for now.
- Names are read as UTF-8, as writers that set the UTF-8 flag write them. A name that is not valid UTF-8 reads as empty and is rejected by the gate. The CP437 reading for names without the UTF-8 flag is not implemented.
- ZIP names use `/` as the separator. A backslash inside a name is an ordinary character here, not a separator. Whether the gate should turn away backslashes is an open question in the plan issue for this repo.
- There is no ZIP writer in this slice.
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
- `ZipPilot/Verify.lean`: the axiom check.
- `Main.lean`: the command line front end.
- `tests/run_tests.py`: differential tests against Python's `zipfile`.
