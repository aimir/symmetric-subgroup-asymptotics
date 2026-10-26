/-
Copyright (c) 2026 Kenta.
Released under Apache-2.0 (provenance/CFSG/Apache-2.0.txt).
Adapted from KitaKen1/finite-simple-groups-lean at 7f09e33a9ceef6b59ce03e34cd4f0558c763e325.
Changes: publication import paths and isolated original-model namespace.
Original generators, certificate data, proof bodies and scoped proof settings are retained.
This actual permutation model is not identified here with the pinned presentation model.
Authors: Kenta
AI usage: Developed with assistance from Claude Code (Fable 5, 1M context,
high reasoning).
-/
import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu23.GeneratedSubgroup
import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu23.Certificates.ChainOrbits
import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu23.Certificates.FinalStabilizer

/-!
# Cardinality proof workspace

The route is a verified stabilizer-chain certificate proving
`Nat.card Sporadic.M23 = 10200960` along the base `22, 0, 1, 2, 5, 3` with
orbit sizes `23, 22, 21, 20, 16, 3` and a trivial final stabilizer.
-/

namespace CFSG.Certificates.Mathieu23

namespace M23Cardinality

open M23Certificates M23Certificates.ChainOrbits M23Certificates.SteinerSystem
open M23Certificates.FinalStabilizer

/-- Stabilizer of the first base point in the 23-point action. -/
abbrev Stab22 : Type :=
  MulAction.stabilizer M23 (22 : Fin 23)

/-- Stabilizer of the first two base points `22,0`. -/
abbrev Stab220 : Type :=
  MulAction.stabilizer Stab22 (0 : Fin 23)

/-- Stabilizer of the first three base points `22,0,1`. -/
abbrev Stab2201 : Type :=
  MulAction.stabilizer Stab220 (1 : Fin 23)

/-- Stabilizer of the first four base points `22,0,1,2`. -/
abbrev Stab22012 : Type :=
  MulAction.stabilizer Stab2201 (2 : Fin 23)

/-- Stabilizer of the first five base points `22,0,1,2,5`. -/
abbrev Stab220125 : Type :=
  MulAction.stabilizer Stab22012 (5 : Fin 23)

/-- Stabilizer of all six base points `22,0,1,2,5,3`. -/
abbrev StabBase : Type :=
  MulAction.stabilizer Stab220125 (3 : Fin 23)

/-- The order expected from the verified orbit chain. -/
theorem target_order_arithmetic : 23 * 22 * 21 * 20 * 16 * 3 = 10200960 := by
  norm_num

/-- The first orbit-stabilizer step: `|M23| = 23 * |Stab22|`. -/
theorem card_M23_eq_first_orbit_mul_stabilizer :
    Nat.card M23 = 23 * Nat.card Stab22 := by
  classical
  rw [Nat.card_eq_fintype_card,
    ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group M23 (22 : Fin 23)]
  rw [Set.fintypeCard_eq_ncard, ChainOrbits.orbit_last_ncard]
  rw [← Nat.card_eq_fintype_card (α := Stab22)]

/-- The second orbit-stabilizer step: `|Stab22| = 22 * |Stab220|`. -/
theorem card_stab22_eq_second_orbit_mul_stabilizer :
    Nat.card Stab22 = 22 * Nat.card Stab220 := by
  classical
  rw [Nat.card_eq_fintype_card,
    ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group Stab22 (0 : Fin 23)]
  rw [Set.fintypeCard_eq_ncard, ChainOrbits.stab22_orbit_zero_ncard]
  rw [← Nat.card_eq_fintype_card (α := Stab220)]

/-- The third orbit-stabilizer step: `|Stab220| = 21 * |Stab2201|`. -/
theorem card_stab220_eq_third_orbit_mul_stabilizer :
    Nat.card Stab220 = 21 * Nat.card Stab2201 := by
  classical
  rw [Nat.card_eq_fintype_card,
    ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group Stab220 (1 : Fin 23)]
  rw [Set.fintypeCard_eq_ncard, ChainOrbits.stab220_orbit_one_ncard]
  rw [← Nat.card_eq_fintype_card (α := Stab2201)]

/-- The fourth orbit-stabilizer step: `|Stab2201| = 20 * |Stab22012|`. -/
theorem card_stab2201_eq_fourth_orbit_mul_stabilizer :
    Nat.card Stab2201 = 20 * Nat.card Stab22012 := by
  classical
  rw [Nat.card_eq_fintype_card,
    ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group Stab2201 (2 : Fin 23)]
  rw [Set.fintypeCard_eq_ncard, ChainOrbits.stab2201_orbit_two_ncard]
  rw [← Nat.card_eq_fintype_card (α := Stab22012)]

/-- The fifth orbit-stabilizer step: `|Stab22012| = 16 * |Stab220125|`. -/
theorem card_stab22012_eq_fifth_orbit_mul_stabilizer :
    Nat.card Stab22012 = 16 * Nat.card Stab220125 := by
  classical
  rw [Nat.card_eq_fintype_card,
    ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group Stab22012 (5 : Fin 23)]
  rw [Set.fintypeCard_eq_ncard, ChainOrbits.stab22012_orbit_five_ncard]
  rw [← Nat.card_eq_fintype_card (α := Stab220125)]

/-- The sixth orbit-stabilizer step: `|Stab220125| = 3 * |StabBase|`. -/
theorem card_stab220125_eq_sixth_orbit_mul_stabilizer :
    Nat.card Stab220125 = 3 * Nat.card StabBase := by
  classical
  rw [Nat.card_eq_fintype_card,
    ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group Stab220125 (3 : Fin 23)]
  rw [Set.fintypeCard_eq_ncard, ChainOrbits.stab220125_orbit_three_ncard]
  rw [← Nat.card_eq_fintype_card (α := StabBase)]

/--
The verified stabilizer-chain data reduces the cardinality theorem to the
final stabilizer certificate.
-/
theorem card_M23_eq_target_mul_final_stabilizer :
    Nat.card M23 = 10200960 * Nat.card StabBase := by
  rw [card_M23_eq_first_orbit_mul_stabilizer,
    card_stab22_eq_second_orbit_mul_stabilizer,
    card_stab220_eq_third_orbit_mul_stabilizer,
    card_stab2201_eq_fourth_orbit_mul_stabilizer,
    card_stab22012_eq_fifth_orbit_mul_stabilizer,
    card_stab220125_eq_sixth_orbit_mul_stabilizer]
  ring

/-- Elements of the final stabilizer fix the base point `22`. -/
theorem stabBase_fixes_last (g : StabBase) : g.1.1.1.1.1.1.1 22 = 22 := by
  have hmem : g.1.1.1.1.1.1 ∈ MulAction.stabilizer M23 (22 : Fin 23) :=
    g.1.1.1.1.1.2
  have hfix := MulAction.mem_stabilizer_iff.mp hmem
  change g.1.1.1.1.1.1.1 (22 : Fin 23) = 22
  simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hfix

/-- Elements of the final stabilizer fix the base point `0`. -/
theorem stabBase_fixes_zero (g : StabBase) : g.1.1.1.1.1.1.1 0 = 0 := by
  have hmem : g.1.1.1.1.1 ∈ MulAction.stabilizer Stab22 (0 : Fin 23) :=
    g.1.1.1.1.2
  have hfix := MulAction.mem_stabilizer_iff.mp hmem
  change g.1.1.1.1.1.1.1 (0 : Fin 23) = 0
  simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hfix

/-- Elements of the final stabilizer fix the base point `1`. -/
theorem stabBase_fixes_one (g : StabBase) : g.1.1.1.1.1.1.1 1 = 1 := by
  have hmem : g.1.1.1.1 ∈ MulAction.stabilizer Stab220 (1 : Fin 23) :=
    g.1.1.1.2
  have hfix := MulAction.mem_stabilizer_iff.mp hmem
  change g.1.1.1.1.1.1.1 (1 : Fin 23) = 1
  simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hfix

/-- Elements of the final stabilizer fix the base point `2`. -/
theorem stabBase_fixes_two (g : StabBase) : g.1.1.1.1.1.1.1 2 = 2 := by
  have hmem : g.1.1.1 ∈ MulAction.stabilizer Stab2201 (2 : Fin 23) :=
    g.1.1.2
  have hfix := MulAction.mem_stabilizer_iff.mp hmem
  change g.1.1.1.1.1.1.1 (2 : Fin 23) = 2
  simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hfix

/-- Elements of the final stabilizer fix the base point `5`. -/
theorem stabBase_fixes_five (g : StabBase) : g.1.1.1.1.1.1.1 5 = 5 := by
  have hmem : g.1.1 ∈ MulAction.stabilizer Stab22012 (5 : Fin 23) := g.1.2
  have hfix := MulAction.mem_stabilizer_iff.mp hmem
  change g.1.1.1.1.1.1.1 (5 : Fin 23) = 5
  simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hfix

/-- Elements of the final stabilizer fix the base point `3`. -/
theorem stabBase_fixes_three (g : StabBase) : g.1.1.1.1.1.1.1 3 = 3 := by
  have hmem : g.1 ∈ MulAction.stabilizer Stab220125 (3 : Fin 23) := g.2
  have hfix := MulAction.mem_stabilizer_iff.mp hmem
  change g.1.1.1.1.1.1.1 (3 : Fin 23) = 3
  simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hfix

/--
The final six-point stabilizer is trivial, using the checked block
certificates and forced propagation.
-/
theorem final_stabilizer_eq_one (g : StabBase) : g = 1 := by
  have hperm : g.1.1.1.1.1.1.1 = (1 : Perm23) := by
    exact fixed_base_preserves_heptads_eq_one g.1.1.1.1.1.1.1
      (M23_preserves_heptads g.1.1.1.1.1.1).1
      (stabBase_fixes_last g)
      (stabBase_fixes_zero g)
      (stabBase_fixes_one g)
      (stabBase_fixes_two g)
      (stabBase_fixes_five g)
      (stabBase_fixes_three g)
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact Subtype.ext hperm

/-- The final stabilizer has order one. -/
theorem final_stabilizer_card_one : Nat.card StabBase = 1 := by
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_eq_one_iff.mpr ⟨1, fun g => final_stabilizer_eq_one g⟩

/-- The verified stabilizer-chain certificate proves `|M23| = 10200960`. -/
theorem card_M23 : Nat.card M23 = 10200960 := by
  calc
    Nat.card M23 = 10200960 * Nat.card StabBase :=
      card_M23_eq_target_mul_final_stabilizer
    _ = 10200960 * 1 := by rw [final_stabilizer_card_one]
    _ = 10200960 := by norm_num

end M23Cardinality

end CFSG.Certificates.Mathieu23
