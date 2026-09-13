/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import PlatonicSolids

/-!
# Solutions to the Challenge

The declarations of `Challenge.lean`, proved. Importing `PlatonicSolids`
supplies `platonic_solids_3d`, `edges_pos_of_regular`,
`regular_polychora_classification` and the definitions they depend on
(`IsPlatonicPair`, `IsRegular4Polytope`, `schlafliGram`, `schlafliDet`),
with the same names and types as in the Challenge module.
Comparator compares those declarations.

The proofs are split across section-sized modules under `PlatonicSolids/`.
There is no `sorry` in those files.
-/
