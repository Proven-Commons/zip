# Test results

Run by `tests/run_tests.py` against Python's `zipfile` module and an independent implementation of the extraction spec in the same file. This record covers slice 1 (stored entries) and slice 2 (deflate) together; the slice 1 record alone is in `tests/TEST-RESULTS-slice1.md`.
Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release). Python: 3.12.3.

- Seed: 20261025
- Archive inputs fed to the Lean reader: 1210
- Checks run: 4502
- Checks passed: 4502
- Failures: 0
- Accepted archives (sections A to C, F): stored entries built by Python zipfile and by hand, with normal, hostile, and cleaning-to-nothing names, plus 600 random archives from the seed; deflated entries written by Python zipfile at levels 0, 1, 6, and 9 over text, random, repeated, empty, and about 70 KB entries; and a mixed stored and deflated archive.
- Turned away with exit code 1 (section D): empty file, random garbage, three truncations, a method 8 entry whose data is not a deflate stream, an encryption flag, a data descriptor, ZIP64 sentinel sizes, a ZIP64 extra field, a ZIP64 locator, a wrong CRC, a local name that differs from the central name, a wrong entry count, and a central size that runs past the directory.
- Raw stream differential (section G): 580 deflate streams wrapped in hand-built method 8 archives: zlib streams at levels 0, 1, 6, 9 with the default, fixed, RLE, and filtered strategies over five inputs, plus 500 mutated streams (byte flips and cuts, seed above). The Lean reader must accept exactly when zlib decompresses the stream to the archived plain data and reaches the end of the stream.
- Dynamic blocks (section G): 18 of 80 generated streams open with a dynamic Huffman block, and the suite asserts the count is above zero, so the dynamic path is exercised on the record.
- Size caps (section H): a deflated entry whose header declares 268435457 plain bytes over a five byte stream is turned away; an honest entry of 268435457 zero bytes (about 260 KB deflated) is turned away; an honest entry of 10000000 zero bytes (about 1028 to 1) is turned away by the ratio cap; and a patterned entry of 1004000 bytes at about 238 to 1 still extracts byte for byte.
- Timing (section T): one entry of 2097152 plain bytes of repeated text, deflated by zlib at level 6 with the fixed Huffman strategy, read by `list` in 0.13 seconds. Before the bit reader carried its remaining count in its state, the same read on the same machine took 9.23 seconds. On a match-heavy dynamic corpus (random text over a 16 letter alphabet, level 6), the old reader took 74.86 seconds at 131072 plain bytes and 189.45 seconds at 262144, and did not finish a 524288 byte entry within a 200 second guard. After the change, those dynamic reads take 0.12 seconds at 131072 bytes and 0.30 seconds at 524288, measured on the same machine. The carried count makes each read cost the same whatever the stream size, where the old reader measured the whole remaining bit list on every read.
- Axiom check (section E): the four slice 1 theorems and the two deflate round trip theorems, `inflate_deflateStored` and `inflate_deflateFixed`, depend only on the standard axioms (see below); no `sorryAx` anywhere.

Axiom check (`ZipPilot/Verify.lean`):

```
'ZipPilot.gate_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZipPilot.cleanComponents_sound' depends on axioms: [propext]
'ZipPilot.extractAll_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZipPilot.extractArchive_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZipPilot.inflate_deflateStored' depends on axioms: [propext, Quot.sound]
'ZipPilot.inflate_deflateFixed' depends on axioms: [propext, Quot.sound]
```
