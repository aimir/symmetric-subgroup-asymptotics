/-
Copyright (c) 2026 Kenta. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: Kenta; adapted to this standalone catalogue.

The two literal permutations are adapted from KitaKen1/finite-simple-groups-lean,
revision 7f09e33a9ceef6b59ce03e34cd4f0558c763e325,
FiniteSimpleGroups/Sporadic/M22/Permutations.lean, declarations m22a and m22b.
The source's design/order certificates are NOT imported as axioms or assumed
verified here. See the semantic audit for the identification obligation.
-/
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Algebra.Group.Subgroup.Basic

namespace CFSG.Models.Mathieu22Construction

def a : Equiv.Perm (Fin 22) :=
  List.formPerm ([0, 11, 4, 5, 15] : List (Fin 22)) *
    List.formPerm ([1, 14, 21, 10, 18] : List (Fin 22)) *
    List.formPerm ([2, 7, 8, 16, 12] : List (Fin 22)) *
    List.formPerm ([3, 13, 9, 19, 20] : List (Fin 22))

def b : Equiv.Perm (Fin 22) :=
  List.formPerm ([0, 17, 10, 19, 18, 8, 3, 1] : List (Fin 22)) *
    List.formPerm ([2, 14] : List (Fin 22)) *
    List.formPerm ([4, 7, 6, 15] : List (Fin 22)) *
    List.formPerm ([5, 21, 12, 13, 9, 11, 16, 20] : List (Fin 22))

abbrev Model := ↥(Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin 22))))

end CFSG.Models.Mathieu22Construction

namespace CFSG.Models
abbrev Mathieu22 := Mathieu22Construction.Model
end CFSG.Models
