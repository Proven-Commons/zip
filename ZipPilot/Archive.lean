/-
  Whole-archive parsing and extraction.

  The extraction rule is the proved part, together with the path gate
  in `Path.lean`: `extractAll` only emits a path built as
  `dest ++ rel`, where `rel` passed the gate, and the theorem
  `extractAll_safe` states that every emitted relative path has no
  `..`, no empty component, no `.`, and is not empty.

  Parsing is covered by differential tests against Python's `zipfile`
  module (see `tests/`), not by a proof.
-/

import ZipPilot.Path
import ZipPilot.Header
import ZipPilot.Crc32

namespace ZipPilot

/-- One archive entry as parsed: a name, whether it is a directory
    entry (its name ends with `/`), and its stored bytes. -/
structure RawEntry where
  name : String
  isDir : Bool
  data : ByteArray

/-- Read one entry's data through its local file header. The local
    header must agree with the central directory on the name, the
    flags, the method, the CRC, and both sizes. The data must end
    before the central directory starts, and its CRC-32 must match
    the headers, so a damaged entry is turned away whole. -/
def readEntry (data : ByteArray) (cdStart : Nat) (e : CentralEntry) :
    Option RawEntry :=
  let lo := e.localOffset
  if lo + 30 > cdStart then none
  else if u32 data lo ≠ 0x04034b50 then none
  else
    let lflags := u16 data (lo + 6)
    let lmethod := u16 data (lo + 8)
    let lcrc := u32 data (lo + 14)
    let lcomp := u32 data (lo + 18)
    let lsize := u32 data (lo + 22)
    let lnLen := u16 data (lo + 26)
    let lxLen := u16 data (lo + 28)
    let dStart := lo + 30 + lnLen + lxLen
    let dEnd := dStart + e.compSize
    if lflags ≠ e.flags ∨ lmethod ≠ e.method ∨ lcrc ≠ e.crc ∨
        lcomp ≠ e.compSize ∨ lsize ≠ e.size then none
    else if bytesToName (sliceList data (lo + 30) lnLen) ≠ e.name then none
    else if dEnd > cdStart then none
    else match extraHasZip64 data (lo + 30 + lnLen) lxLen with
      | none => none
      | some true => none
      | some false =>
        let bytes := data.extract dStart dEnd
        if (Crc32.crc32 bytes.toList).toNat ≠ e.crc then none
        else some { name := e.name, isDir := e.name.endsWith "/",
                    data := bytes }

/-- Parse a whole archive. The end record is read first, then the
    central directory it points at, then each entry through its local
    header. A ZIP64 end record or locator turns the archive away, as
    do truncated records, a directory that does not end where the end
    record begins, and any entry the header checks turn away. -/
def parseArchive (data : ByteArray) : Option (List RawEntry) := do
  let eocdPos ← findEocd data
  if eocdPos ≥ 20 ∧ u32 data (eocdPos - 20) = 0x07064b50 then none
  else
    let e ← parseEocd data eocdPos
    let (centrals, cdEnd) ← parseCentral data e.count e.cdOffset
    if cdEnd ≠ eocdPos then none
    else centrals.mapM (readEntry data e.cdOffset)

/-- File entries are extracted. Directory entries are not, so a
    directory name cannot be used to place a later entry outside the
    destination. -/
def isFile (e : RawEntry) : Bool :=
  !e.isDir

/-- Extract entries into a list of `(path, data)` pairs, in memory.
    The path of each pair is the destination components followed by
    the gated relative components of the entry name. -/
def extractAll (dest : List String) (entries : List RawEntry) :
    List (List String × ByteArray) :=
  entries.filterMap fun e =>
    if isFile e then
      (gate e.name).map fun rel => (dest ++ rel, e.data)
    else none

/-- Every path `extractAll` emits is the destination followed by a
    gated relative path: no `..`, no empty component, no `.`, and the
    relative path is not empty. So no emitted path escapes the
    destination. -/
theorem extractAll_safe : ∀ (dest : List String) (entries : List RawEntry)
    (path : List String) (bytes : ByteArray),
    (path, bytes) ∈ extractAll dest entries →
    ∃ rel, path = dest ++ rel ∧
      ".." ∉ rel ∧ "" ∉ rel ∧ "." ∉ rel ∧ rel ≠ [] := by
  intro dest entries path bytes h
  unfold extractAll at h
  rw [List.mem_filterMap] at h
  obtain ⟨e, _, hfe⟩ := h
  by_cases hfile : isFile e
  · rw [if_pos hfile] at hfe
    cases hg : gate e.name with
    | none =>
      rw [hg] at hfe
      simp at hfe
    | some rel =>
      rw [hg] at hfe
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hfe
      obtain ⟨hpath, _⟩ := hfe
      obtain ⟨h1, h2, h3, h4⟩ := gate_sound e.name rel hg
      exact ⟨rel, hpath.symm, h1, h2, h3, h4⟩
  · rw [if_neg hfile] at hfe
    exact absurd hfe (by simp)

/-- Parse, then extract. -/
def extractArchive (dest : List String) (data : ByteArray) :
    Option (List (List String × ByteArray)) :=
  (parseArchive data).map (extractAll dest)

/-- The same guarantee for a whole archive read from bytes. -/
theorem extractArchive_safe : ∀ (dest : List String) (data : ByteArray)
    (out : List (List String × ByteArray)) (path : List String)
    (bytes : ByteArray),
    extractArchive dest data = some out → (path, bytes) ∈ out →
    ∃ rel, path = dest ++ rel ∧
      ".." ∉ rel ∧ "" ∉ rel ∧ "." ∉ rel ∧ rel ≠ [] := by
  intro dest data out path bytes h hmem
  unfold extractArchive at h
  cases hp : parseArchive data with
  | none =>
    rw [hp] at h
    simp at h
  | some entries =>
    rw [hp] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact extractAll_safe dest entries path bytes hmem

end ZipPilot
