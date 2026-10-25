# Test results

Run by `tests/run_tests.py` against Python's `zipfile` module and an independent implementation of the extraction spec in the same file.
Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release). Python: 3.12.3.

- Seed: 20261025
- Archive inputs fed to the Lean reader: 620
- Checks run: 3058
- Checks passed: 3058
- Failures: 0
- Accepted archives: stored entries built by Python zipfile and by hand, with normal, hostile, and cleaning-to-nothing names, plus 600 random archives from the seed.
- Turned away with exit code 1: empty file, random garbage, three truncations, a deflated entry, a method 8 entry, an encryption flag, a data descriptor, ZIP64 sentinel sizes, a ZIP64 extra field, a ZIP64 locator, a wrong CRC, a local name that differs from the central name, a wrong entry count, and a central size that runs past the directory.

Axiom check (`ZipPilot/Verify.lean`):

```
'ZipPilot.gate_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZipPilot.cleanComponents_sound' depends on axioms: [propext]
'ZipPilot.extractAll_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZipPilot.extractArchive_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
```
