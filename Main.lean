/-
  Command line front end for the ZIP reader.

    zip-pilot list <file.zip>
      Print one line per entry: name, data size, and `file` or `dir`.

    zip-pilot manifest <file.zip> <dest>
      Print what extraction would do, in archive order, without
      writing anything to disk:
        OK     <dest path> <size> <byte sum>   for an extracted file
        REJECT <name>                          for a file whose name
                                               fails the path gate
        SKIP   <name> directory                for a directory entry

  An archive the parser turns away (truncated, malformed, or holding
  an entry outside the first slice: another compression method,
  ZIP64, encryption, or a data descriptor) prints an error to stderr
  and exits with code 1 for both commands.
-/

import ZipPilot

open ZipPilot

def byteSum (b : ByteArray) : Nat :=
  b.toList.foldl (fun a x => a + x.toNat) 0

def runList (file : String) : IO UInt32 := do
  let data ← IO.FS.readBinFile file
  match parseArchive data with
  | none =>
    IO.eprintln s!"error: cannot parse {file} as a zip archive"
    return 1
  | some entries =>
    for e in entries do
      IO.println s!"{e.name}\t{e.data.size}\t{if e.isDir then "dir" else "file"}"
    return 0

def runManifest (file dest : String) : IO UInt32 := do
  let data ← IO.FS.readBinFile file
  match parseArchive data with
  | none =>
    IO.eprintln s!"error: cannot parse {file} as a zip archive"
    return 1
  | some entries =>
    let destCs := if dest = "" then [] else dest.splitOn "/"
    for e in entries do
      if e.isDir then
        IO.println s!"SKIP\t{e.name}\tdirectory"
      else
        match gate e.name with
        | none => IO.println s!"REJECT\t{e.name}"
        | some rel =>
          let path := String.intercalate "/" (destCs ++ rel)
          IO.println s!"OK\t{path}\t{e.data.size}\t{byteSum e.data}"
    return 0

def usage : IO UInt32 := do
  IO.eprintln "usage: zip-pilot list <file.zip>"
  IO.eprintln "       zip-pilot manifest <file.zip> <dest>"
  return 2

def main (args : List String) : IO UInt32 := do
  match args with
  | ["list", file] => runList file
  | ["manifest", file, dest] => runManifest file dest
  | _ => usage
