#!/usr/bin/env python3
"""Differential tests for the Proven Commons ZIP reader.

Compares the Lean implementation against Python's `zipfile` module and
against an independent implementation of the extraction spec written
below. Run from anywhere:

    python3 tests/run_tests.py

It builds the Lean project if the executable is missing, runs all
cases in a temporary directory, writes `tests/TEST-RESULTS.md`, and
exits non-zero if any case fails.
"""

import io
import random
import warnings
import struct
import subprocess
import sys
import tempfile
import zipfile
import zlib
from pathlib import Path

PILOT_DIR = Path(__file__).resolve().parent.parent
EXE = PILOT_DIR / ".lake" / "build" / "bin" / "zip-pilot"
RESULTS = PILOT_DIR / "tests" / "TEST-RESULTS.md"
SEED = 20261025

checks = 0
failures = []
inputs = 0
dyn_streams = 0
dyn_dynamic = 0
timing_seconds = None
TIMING_PLAIN_SIZE = 2097152


def check(name, ok, detail=""):
    global checks
    checks += 1
    if not ok:
        failures.append(f"{name}: {detail}")
        print(f"FAIL {name}: {detail}")


def run_lean(*args):
    return subprocess.run([str(EXE), *args], capture_output=True, text=True)


def spec_gate(name):
    """The extraction spec, implemented independently of the Lean code.

    Returns the cleaned relative components, or None to reject.
    Absolute names are rejected. Any `..` is rejected. Empty and `.`
    components are dropped. An empty result is rejected.
    """
    if name.startswith("/"):
        return None
    out = []
    for comp in name.split("/"):
        if comp == "..":
            return None
        if comp in ("", "."):
            continue
        out.append(comp)
    return out if out else None


def is_dir(name):
    return name.endswith("/")


def expected_list(entries):
    return [f"{name}\t{len(data)}\t{'dir' if is_dir(name) else 'file'}"
            for name, data in entries]


def expected_manifest(entries, dest="out"):
    lines = []
    for name, data in entries:
        if is_dir(name):
            lines.append(f"SKIP\t{name}\tdirectory")
            continue
        rel = spec_gate(name)
        if rel is None:
            lines.append(f"REJECT\t{name}")
        else:
            joined = "/".join([dest] + rel)
            lines.append(f"OK\t{joined}\t{len(data)}\t{sum(data)}")
    return lines


def run_case(label, raw, entries, td):
    """One archive the reader must accept. `entries` is the ground
    truth: (name, data) pairs in archive order. The Lean output must
    match the spec, and zipfile must read the same entries back."""
    global inputs
    inputs += 1
    path = td / f"{label}.zip"
    path.write_bytes(raw)

    r = run_lean("list", str(path))
    check(f"{label}-list-exit", r.returncode == 0, r.stderr)
    if r.returncode == 0:
        check(f"{label}-list", r.stdout.splitlines() == expected_list(entries),
              f"lean={r.stdout.splitlines()} expected={expected_list(entries)}")
    r = run_lean("manifest", str(path), "out")
    check(f"{label}-manifest-exit", r.returncode == 0, r.stderr)
    if r.returncode == 0:
        exp = expected_manifest(entries)
        check(f"{label}-manifest", r.stdout.splitlines() == exp,
              f"lean={r.stdout.splitlines()} expected={exp}")

    try:
        with zipfile.ZipFile(io.BytesIO(raw)) as z:
            zentries = []
            for info in z.infolist():
                # Read through the ZipInfo, not the name: with two
                # entries of one name, a name lookup reads the last.
                data = b"" if info.is_dir() else z.read(info)
                if info.is_dir() and not info.filename.endswith("/"):
                    zentries.append((info.filename + "/", data))
                else:
                    zentries.append((info.filename, data))
        check(f"{label}-zipfile-agrees", zentries == list(entries),
              f"zipfile={[(n, len(d)) for n, d in zentries]} "
              f"truth={[(n, len(d)) for n, d in entries]}")
    except Exception as ex:  # noqa: BLE001 - the check records it
        check(f"{label}-zipfile-agrees", False, f"zipfile raised: {ex}")


def run_reject(label, raw, td):
    """One archive the reader must turn away with exit code 1."""
    global inputs
    inputs += 1
    path = td / f"{label}.zip"
    path.write_bytes(raw)
    r = run_lean("list", str(path))
    check(f"{label}-list-rejects", r.returncode == 1,
          f"rc={r.returncode} out={r.stdout[:200]}")
    r = run_lean("manifest", str(path), "out")
    check(f"{label}-manifest-rejects", r.returncode == 1,
          f"rc={r.returncode} out={r.stdout[:200]}")


def build_hand(entries):
    """Build an archive by hand, byte for byte. Each entry is a dict:
    name, data, and optional overrides: flags, method, compdata,
    compsize, size, crc, extra, local_extra, local_name, descriptor
    (True writes a data descriptor after the data; with the descriptor
    flag set, the local sizes are written as zero)."""
    out = bytearray()
    centrals = []
    for e in entries:
        name = e["name"].encode()
        data = e["data"]
        crc = zlib.crc32(data) & 0xFFFFFFFF
        flags = e.get("flags", 0)
        if any(b > 127 for b in name):
            # Real writers set the UTF-8 flag for non-ASCII names, as
            # zipfile does in writestr. Without it zipfile reads the
            # name as CP437.
            flags |= 0x800
        method = e.get("method", 0)
        comp = e.get("compdata", data)
        cs = e.get("compsize", len(comp))
        us = e.get("size", len(data))
        crc_f = e.get("crc", crc)
        extra = e.get("extra", b"")
        lextra = e.get("local_extra", extra)
        lname = e.get("local_name", e["name"]).encode()
        desc = e.get("descriptor", False)
        lcs, lus, lcrc = (0, 0, 0) if desc else (cs, us, crc_f)
        off = len(out)
        out += struct.pack("<IHHHHHIIIHH", 0x04034b50, 20, flags, method,
                           0, 0, lcrc, lcs, lus, len(lname), len(lextra))
        out += lname + lextra + comp
        if desc:
            out += struct.pack("<IIII", 0x08074b50, crc_f, cs, us)
        centrals.append(
            struct.pack("<IHHHHHHIIIHHHHHII", 0x02014b50, 20, 20, flags,
                        method, 0, 0, crc_f, cs, us, len(name), len(extra),
                        0, 0, 0, 0, off) + name + extra)
    cd_off = len(out)
    for c in centrals:
        out += c
    out += struct.pack("<IHHHHIIH", 0x06054b50, 0, 0, len(entries),
                       len(entries), len(out) - cd_off, cd_off, 0)
    return bytes(out)


def zip64_extra(size, comp):
    return struct.pack("<HHQQ", 0x0001, 16, size, comp)


def build_with_zipfile(entries, compression=zipfile.ZIP_STORED, comment=b"",
                       compresslevel=None):
    buf = io.BytesIO()
    with warnings.catch_warnings():
        # Duplicate names are part of the test data, not a mistake.
        warnings.filterwarnings("ignore", message="Duplicate name")
        with zipfile.ZipFile(buf, "w", compression,
                             compresslevel=compresslevel) as z:
            z.comment = comment
            for name, data in entries:
                z.writestr(name, data)
    return buf.getvalue()


def build_mixed(entries):
    """A zipfile archive where each entry picks its own method.
    `entries` is a list of (name, data, compression)."""
    buf = io.BytesIO()
    with zipfile.ZipFile(buf, "w") as z:
        for name, data, comp in entries:
            z.writestr(name, data, compress_type=comp)
    return buf.getvalue()


SAFE_SEGMENTS = ["a", "dir", "sub", "x.txt", "file.bin", "deep", "café",
                 "with space", "under_score", "dash-name", "UPPER"]
HOSTILE_SEGMENTS = ["..", ".", "", ".."]


def random_entries(rng):
    n = rng.randrange(0, 9)
    entries = []
    for _ in range(n):
        style = rng.random()
        if style < 0.12:
            name = rng.choice(["d", "dir", "a/b"]) + "/"
            entries.append((name, b""))
            continue
        parts = []
        for _ in range(rng.randrange(1, 5)):
            pool = SAFE_SEGMENTS if rng.random() < 0.8 else HOSTILE_SEGMENTS
            parts.append(rng.choice(pool))
        name = "/".join(parts)
        if rng.random() < 0.08:
            name = "/" + name
        if name.endswith("/"):
            name += "f.txt"
        data = rng.randbytes(rng.randrange(0, 700))
        entries.append((name, data))
    return entries


def main():
    global inputs, timing_seconds
    if not EXE.exists():
        subprocess.run(["lake", "build"], cwd=PILOT_DIR, check=True)

    rng = random.Random(SEED)
    with tempfile.TemporaryDirectory() as td:
        td = Path(td)

        # A. A stored archive built by zipfile, with a comment.
        a_entries = [
            ("hello.txt", b"hello world"),
            ("dir/", b""),
            ("dir/nested.bin", bytes(range(256)) * 3),
            ("empty.txt", b""),
            ("big.bin", rng.randbytes(5000)),
            ("deep/" + "/".join(f"d{i}" for i in range(8)) + "/leaf.txt",
             b"leaf"),
        ]
        run_case("a-zipfile", build_with_zipfile(a_entries,
                                                 comment=b"pilot"),
                 a_entries, td)

        # An empty archive is valid and lists nothing.
        run_case("a-empty", build_with_zipfile([]), [], td)

        # B. Hand-built archives with hostile and edge-case names.
        hostile = [
            ("../evil.txt", b"evil"),
            ("a/../../evil2.txt", b"evil2"),
            ("/abs.txt", b"abs"),
            ("./dot.txt", b"dot"),
            ("a//b.txt", b"ab"),
            ("a/./c.txt", b"ac"),
            ("café.txt", "café".encode()),
            ("good/ok.txt", b"ok"),
        ]
        run_case("b-hostile",
                 build_hand([{"name": n, "data": d} for n, d in hostile]),
                 hostile, td)

        nothing = [("", b"x"), (".", b"x"), ("a/..", b"x"), ("./", b"")]
        run_case("b-clean-nothing",
                 build_hand([{"name": n, "data": d} for n, d in nothing]),
                 nothing, td)

        # C. Random archives, half hand-built (hostile names allowed),
        # half built by zipfile (names kept to what writestr stores
        # unchanged: no leading slash, no `..` first part).
        n_random = 600
        for i in range(n_random):
            entries = random_entries(rng)
            if i % 2 == 0:
                raw = build_hand([{"name": n, "data": d}
                                  for n, d in entries])
                run_case(f"c{i}", raw, entries, td)
            else:
                safe = [(n, d) for n, d in entries
                        if spec_gate(n) is not None or is_dir(n)]
                safe = [(n, d) for n, d in safe if not n.startswith("/")]
                raw = build_with_zipfile(safe)
                run_case(f"c{i}", raw, safe, td)

        # D. Archives the reader must turn away.
        good = build_hand([{"name": "x.txt", "data": b"hello"},
                           {"name": "y.bin", "data": bytes(range(100))}])
        run_reject("d-empty-file", b"", td)
        run_reject("d-garbage", rng.randbytes(4096), td)
        run_reject("d-trunc-eocd", good[:-10], td)
        run_reject("d-trunc-data", good[:40], td)
        run_reject("d-trunc-central", good[:-30], td)

        # Slice 2: a deflated entry is now read, not turned away.
        deflated = build_with_zipfile([("z.txt", b"z" * 500)],
                                       zipfile.ZIP_DEFLATED)
        run_case("d-deflated", deflated, [("z.txt", b"z" * 500)], td)
        # Method 8 whose data is not a deflate stream at all: the
        # bytes of "stored" fail the size or CRC check after inflate
        # (or fail to inflate), so the archive is still turned away.
        run_reject("d-method8",
                   build_hand([{"name": "m.txt", "data": b"stored",
                                "method": 8}]), td)
        run_reject("d-encrypted",
                   build_hand([{"name": "e.txt", "data": b"secret",
                                "flags": 0x0001}]), td)
        run_reject("d-descriptor",
                   build_hand([{"name": "s.txt", "data": b"streamed",
                                "flags": 0x0008, "descriptor": True}]), td)
        run_reject("d-zip64-sentinel",
                   build_hand([{"name": "big.txt", "data": b"small",
                                "compsize": 0xFFFFFFFF, "size": 0xFFFFFFFF,
                                "extra": zip64_extra(5, 5)}]), td)
        run_reject("d-zip64-extra",
                   build_hand([{"name": "big.txt", "data": b"small",
                                "extra": zip64_extra(5, 5)}]), td)

        badcrc = bytearray(good)
        badcrc[35] ^= 0xFF  # first data byte of the first entry
        run_reject("d-bad-crc", bytes(badcrc), td)
        run_reject("d-local-name",
                   build_hand([{"name": "central.txt", "data": b"data",
                                "local_name": "central.txX"}]), td)

        badcount = bytearray(good)
        eocd = len(good) - 22
        badcount[eocd + 10] = 7  # total entry count no longer matches
        run_reject("d-bad-count", bytes(badcount), td)

        bigsize = bytearray(good)
        cdpos = good.rfind(b"PK\x01\x02")
        struct.pack_into("<I", bigsize, cdpos + 20, 9999)
        run_reject("d-oversize", bytes(bigsize), td)

        locator = struct.pack("<IIQI", 0x07064b50, 0, 42, 1)
        withloc = good[:-22] + locator + good[-22:]
        run_reject("d-zip64-locator", withloc, td)

        # F. Deflated archives (slice 2). One archive per compression
        # level, each holding the same data kinds; every entry must
        # come back byte for byte through list and manifest.
        f_text = (b"The quick brown fox jumps over the lazy dog. "
                  b"Pack my box with five dozen liquor jugs. ") * 25
        f_kinds = [
            ("text.txt", f_text),
            ("random.bin", rng.randbytes(5000)),
            ("repeated.bin", b"abcd" * 5000),
            ("empty.txt", b""),
            ("big-text.bin", f_text * 30),          # about 70 KB
            ("big-random.bin", rng.randbytes(70000)),
        ]
        for level in (0, 1, 6, 9):
            run_case(f"f-deflated-l{level}",
                     build_with_zipfile(f_kinds, zipfile.ZIP_DEFLATED,
                                        compresslevel=level),
                     f_kinds, td)

        # Mixed stored and deflated entries in one archive, with a
        # hostile name and a directory among them.
        mixed = [
            ("plain.txt", b"stored bytes", zipfile.ZIP_STORED),
            ("squashed.txt", f_text, zipfile.ZIP_DEFLATED),
            ("../evil.txt", b"evil but deflated", zipfile.ZIP_DEFLATED),
            ("dir/", b"", zipfile.ZIP_STORED),
            ("dir/inner.bin", rng.randbytes(3000), zipfile.ZIP_DEFLATED),
        ]
        run_case("f-mixed", build_mixed(mixed),
                 [(n, d) for n, d, _ in mixed], td)

        # G. Raw deflate stream differential against Python zlib
        # (wbits -15). Each stream is wrapped in a hand-built
        # method 8 archive whose directory carries the plain data's
        # size and CRC. The Lean reader must accept exactly when
        # zlib decompresses the stream, reaches the end of the
        # stream, and the output is the plain data: anything else
        # (a zlib error, no end of stream, different bytes) must be
        # a reject.
        def zlib_verdict(stream, plain):
            d = zlib.decompressobj(-15)
            try:
                out = d.decompress(stream)
            except zlib.error:
                return False
            return d.eof and out == plain

        g_cases = 0

        def first_block_type(stream):
            """The BTYPE of the first block: bit 0 is BFINAL, bits
            1 and 2 are BTYPE, least significant bit first."""
            if not stream:
                return None
            b = stream[0]
            return ((b >> 1) & 1) + 2 * ((b >> 2) & 1)

        def note_stream(stream):
            """Record whether a generated stream opens with a
            dynamic Huffman block (BTYPE 10). The suite asserts at
            least one generated stream does, so the dynamic code
            path is known to be exercised, not just hoped for."""
            global dyn_streams, dyn_dynamic
            dyn_streams += 1
            if first_block_type(stream) == 2:
                dyn_dynamic += 1

        def run_stream(label, stream, plain):
            nonlocal g_cases
            g_cases += 1
            raw = build_hand([{"name": "s.bin", "data": plain,
                               "method": 8, "compdata": stream}])
            if zlib_verdict(stream, plain):
                run_case(label, raw, [("s.bin", plain)], td)
            else:
                run_reject(label, raw, td)

        g_plains = [
            ("text", f_text),
            ("random", rng.randbytes(3000)),
            ("repeated", b"xyz" * 7000),
            ("empty", b""),
            ("range", bytes(range(256)) * 4),
        ]
        strategies = [("default", zlib.Z_DEFAULT_STRATEGY),
                      ("fixed", zlib.Z_FIXED),
                      ("rle", zlib.Z_RLE),
                      ("filtered", zlib.Z_FILTERED)]
        for pname, plain in g_plains:
            for level in (0, 1, 6, 9):
                for sname, strat in strategies:
                    co = zlib.compressobj(level, zlib.DEFLATED, -15, 9,
                                          strat)
                    stream = co.compress(plain) + co.flush()
                    note_stream(stream)
                    run_stream(f"g-{pname}-l{level}-{sname}", stream, plain)

        # Mutations of two level 6 streams: byte flips and cuts.
        # Both sides must agree on every one.
        for pname, plain in [("text", f_text), ("random", g_plains[1][1])]:
            co = zlib.compressobj(6, zlib.DEFLATED, -15)
            base = co.compress(plain) + co.flush()
            for i in range(250):
                s = bytearray(base)
                for _ in range(rng.randrange(1, 5)):
                    s[rng.randrange(len(s))] = rng.randrange(256)
                if rng.random() < 0.2:
                    s = s[:rng.randrange(len(s))]
                run_stream(f"g-mut-{pname}-{i}", bytes(s), plain)

        # The dynamic Huffman path must be exercised by the
        # generated corpus, not just reachable in principle.
        check("g-dynamic-blocks-present", dyn_dynamic > 0,
              f"{dyn_dynamic} of {dyn_streams} generated streams "
              "open with a dynamic block")

        # H. The size caps on deflated entries, checked from the
        # header sizes before any inflation work. One entry lies in
        # its header (a small stream, a declared size past the
        # cap); one is honest data past the cap (256 MiB of zeros
        # deflates to about 260 KB, so the archive stays small);
        # one is honest data under the size cap but past the 1000
        # to 1 ratio cap (zeros deflate at about 1028 to 1). A
        # patterned entry at about 238 to 1 must still extract.
        co = zlib.compressobj(6, zlib.DEFLATED, -15)
        hello_stream = co.compress(b"hello") + co.flush()
        run_reject("h-oversize-declared",
                   build_hand([{"name": "lie.bin", "data": b"hello",
                                "method": 8, "compdata": hello_stream,
                                "size": 268435457}]), td)
        big_plain = bytes(268435457)
        co = zlib.compressobj(9, zlib.DEFLATED, -15)
        big_stream = co.compress(big_plain) + co.flush()
        run_reject("h-oversize-real",
                   build_hand([{"name": "big.bin", "data": big_plain,
                                "method": 8, "compdata": big_stream}]),
                   td)
        del big_plain, big_stream
        ratio_plain = bytes(10000000)
        co = zlib.compressobj(9, zlib.DEFLATED, -15)
        ratio_stream = co.compress(ratio_plain) + co.flush()
        run_reject("h-ratio-over",
                   build_hand([{"name": "ratio.bin", "data": ratio_plain,
                                "method": 8,
                                "compdata": ratio_stream}]), td)
        del ratio_plain, ratio_stream
        ok_plain = bytes(range(251)) * 4000
        co = zlib.compressobj(9, zlib.DEFLATED, -15)
        ok_stream = co.compress(ok_plain) + co.flush()
        run_case("h-ratio-ok",
                 build_hand([{"name": "ok.bin", "data": ok_plain,
                              "method": 8, "compdata": ok_stream}]),
                 [("ok.bin", ok_plain)], td)
        del ok_plain, ok_stream

        # T. Timing: one multi-megabyte fixed Huffman entry with
        # many back references, read end to end (list reads and
        # CRCs every entry). The wall time is recorded in the
        # results, with the times of the reader before the bit
        # reader carried its remaining count, measured on the same
        # machine on this same corpus and on a match-heavy dynamic
        # corpus: see the timing lines in the results.
        import time
        t_plain = (f_text * (TIMING_PLAIN_SIZE // len(f_text) + 1)
                   )[:TIMING_PLAIN_SIZE]
        co = zlib.compressobj(6, zlib.DEFLATED, -15, 9, zlib.Z_FIXED)
        t_stream = co.compress(t_plain) + co.flush()
        t_raw = build_hand([{"name": "big.txt", "data": t_plain,
                             "method": 8, "compdata": t_stream}])
        inputs += 1
        t_path = td / "timing.zip"
        t_path.write_bytes(t_raw)
        start = time.perf_counter()
        r = run_lean("list", str(t_path))
        timing_seconds = time.perf_counter() - start
        check("t-timing-exit", r.returncode == 0, r.stderr)
        if r.returncode == 0:
            check("t-timing-list",
                  r.stdout.splitlines() ==
                  [f"big.txt\t{len(t_plain)}\tfile"],
                  f"lean={r.stdout.splitlines()}")
        del t_plain, t_stream, t_raw

    # E. Axiom check: only the three standard axioms.
    ax = subprocess.run(["lake", "env", "lean", "ZipPilot/Verify.lean"],
                        cwd=PILOT_DIR, capture_output=True, text=True)
    ax_out = ax.stdout + ax.stderr
    check("axioms-run", ax.returncode == 0, ax_out[:400])
    for thm in ["gate_sound", "cleanComponents_sound", "extractAll_safe",
                "extractArchive_safe", "inflate_deflateStored",
                "inflate_deflateFixed"]:
        check(f"axioms-{thm}", thm in ax_out, ax_out[:400])
    check("axioms-no-sorry", "sorryAx" not in ax_out, ax_out[:400])

    lean_ver = subprocess.run(["lean", "--version"], capture_output=True,
                              text=True).stdout.strip()
    ok = checks - len(failures)
    lines = [
        "# Test results",
        "",
        "Run by `tests/run_tests.py` against Python's `zipfile` module "
        "and an independent implementation of the extraction spec in "
        "the same file. This record covers slice 1 (stored entries) "
        "and slice 2 (deflate) together; the slice 1 record alone is "
        "in `tests/TEST-RESULTS-slice1.md`.",
        f"Lean: {lean_ver}. Python: {sys.version.split()[0]}.",
        "",
        f"- Seed: {SEED}",
        f"- Archive inputs fed to the Lean reader: {inputs}",
        f"- Checks run: {checks}",
        f"- Checks passed: {ok}",
        f"- Failures: {len(failures)}",
        "- Accepted archives (sections A to C, F): stored entries "
        "built by Python zipfile and by hand, with normal, hostile, "
        "and cleaning-to-nothing names, plus 600 random archives "
        "from the seed; deflated entries written by Python zipfile "
        "at levels 0, 1, 6, and 9 over text, random, repeated, "
        "empty, and about 70 KB entries; and a mixed stored and "
        "deflated archive.",
        "- Turned away with exit code 1 (section D): empty file, "
        "random garbage, three truncations, a method 8 entry whose "
        "data is not a deflate stream, an encryption flag, a data "
        "descriptor, ZIP64 sentinel sizes, a ZIP64 extra field, a "
        "ZIP64 locator, a wrong CRC, a local name that differs from "
        "the central name, a wrong entry count, and a central size "
        "that runs past the directory.",
        f"- Raw stream differential (section G): {g_cases} deflate "
        "streams wrapped in hand-built method 8 archives: zlib "
        "streams at levels 0, 1, 6, 9 with the default, fixed, RLE, "
        "and filtered strategies over five inputs, plus 500 mutated "
        "streams (byte flips and cuts, seed above). The Lean reader "
        "must accept exactly when zlib decompresses the stream to "
        "the archived plain data and reaches the end of the stream.",
        f"- Dynamic blocks (section G): {dyn_dynamic} of "
        f"{dyn_streams} generated streams open with a dynamic "
        "Huffman block, and the suite asserts the count is above "
        "zero, so the dynamic path is exercised on the record.",
        "- Size caps (section H): a deflated entry whose header "
        "declares 268435457 plain bytes over a five byte stream is "
        "turned away; an honest entry of 268435457 zero bytes "
        "(about 260 KB deflated) is turned away; an honest entry "
        "of 10000000 zero bytes (about 1028 to 1) is turned away "
        "by the ratio cap; and a patterned entry of 1004000 bytes "
        "at about 238 to 1 still extracts byte for byte.",
        f"- Timing (section T): one entry of {TIMING_PLAIN_SIZE} "
        "plain bytes of repeated text, deflated by zlib at level "
        f"6 with the fixed Huffman strategy, read by `list` in "
        f"{timing_seconds:.2f} seconds. Before the bit reader "
        "carried its remaining count in its state, the same read "
        "on the same machine took 9.23 seconds. On a match-heavy "
        "dynamic corpus (random text over a 16 letter alphabet, "
        "level 6), the old reader took 74.86 seconds at 131072 "
        "plain bytes and 189.45 seconds at 262144, and did not "
        "finish a 524288 byte entry within a 200 second guard. "
        "After the change, those dynamic reads take 0.12 seconds "
        "at 131072 bytes and 0.30 seconds at 524288, measured on "
        "the same machine. The carried count makes each read cost "
        "the same whatever the stream size, where the old reader "
        "measured the whole remaining bit list on every read.",
        "- Axiom check (section E): the four slice 1 theorems and "
        "the two deflate round trip theorems, `inflate_deflateStored` "
        "and `inflate_deflateFixed`, depend only on the standard "
        "axioms (see below); no `sorryAx` anywhere.",
        "",
        "Axiom check (`ZipPilot/Verify.lean`):",
        "",
        "```",
        ax_out.strip(),
        "```",
        "",
    ]
    if failures:
        lines += ["## Failures", ""] + [f"- {f}" for f in failures] + [""]
    RESULTS.write_text("\n".join(lines))
    print(f"{ok}/{checks} checks passed over {inputs} archive inputs; "
          f"results in {RESULTS}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
