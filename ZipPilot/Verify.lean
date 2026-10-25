/-
  Axiom check for the headline theorems. Building this file prints the
  axioms each proof depends on. The expected output is only the three
  standard Lean axioms: `propext`, `Classical.choice`, `Quot.sound`,
  or a subset of them. Any other name here breaks the verified bar.
-/

import ZipPilot.Archive

#print axioms ZipPilot.gate_sound
#print axioms ZipPilot.cleanComponents_sound
#print axioms ZipPilot.extractAll_safe
#print axioms ZipPilot.extractArchive_safe
