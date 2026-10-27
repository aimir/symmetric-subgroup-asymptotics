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
import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu24.Certificates.StabilizerChain

/-!
# Orbit equalities for the stabilizer chain

This file turns the word certificates of `StabilizerChain.lean` into the
seven orbit-size theorems used by the cardinality proof:

* `orbit_last_ncard = 24`,
* `stab23_orbit_22_ncard = 23`,
* `stab2322_orbit_zero_ncard = 22`,
* `stab23220_orbit_one_ncard = 21`,
* `stab232201_orbit_two_ncard = 20`,
* `stab2322012_orbit_five_ncard = 16` (the complement of the block `B0`),
* `stab23220125_orbit_three_ncard = 3` (the rest of the block `B0`).

The upper bounds at the last two levels use the verified block-preservation
certificates: an element fixing `23,22,0,1,2` maps the unique block through
them to itself.
-/

namespace CFSG.Certificates.Mathieu24
namespace M24Certificates
namespace ChainOrbits

open StabilizerChain SteinerSystem

/-! ## Level 1: the orbit of `23` -/

theorem first_orbit_M24_witness (x : Fin 24) :
    ∃ g : M24, g.1 (23 : Fin 24) = x :=
  ⟨Word.toM24 (levelOneWord x), by simpa using levelOneWord_maps_last_all x⟩

theorem orbit_last_eq_univ : MulAction.orbit M24 (23 : Fin 24) = Set.univ := by
  ext x
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _
    obtain ⟨g, hg⟩ := first_orbit_M24_witness x
    exact ⟨g, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg⟩

theorem orbit_last_ncard : (MulAction.orbit M24 (23 : Fin 24)).ncard = 24 := by
  rw [orbit_last_eq_univ, Set.ncard_univ]
  simp

/-! ## Level 2: the stabilizer of `23` moving `22` -/

def lastStabilizerElement (x : Fin 24) (hx : x ≠ 23) :
    MulAction.stabilizer M24 (23 : Fin 24) :=
  ⟨Word.toM24 (levelTwoWord x), by
    rw [MulAction.mem_stabilizer_iff]
    change (Word.eval (levelTwoWord x)) (23 : Fin 24) = 23
    exact levelTwoWord_fixes_23_all x hx⟩

theorem second_orbit_stabilizer_witness (x : Fin 24) (hx : x ≠ 23) :
    ∃ g : MulAction.stabilizer M24 (23 : Fin 24), g.1.1 (22 : Fin 24) = x :=
  ⟨lastStabilizerElement x hx, by
    change (Word.eval (levelTwoWord x)) (22 : Fin 24) = x
    exact levelTwoWord_maps_22_all x hx⟩

theorem stab23_orbit_22_eq :
    MulAction.orbit (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24) =
      {x : Fin 24 | x ≠ 23} := by
  ext x
  constructor
  · rintro ⟨g, hg⟩ hx23
    have hfix : g.1.1 (23 : Fin 24) = 23 := by
      have hg23 := (MulAction.mem_stabilizer_iff.mp g.2)
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg23
    have hmap : g.1.1 (22 : Fin 24) = 23 := by
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx23] using hg
    have h2223 : (22 : Fin 24) = 23 := g.1.1.injective (by rw [hmap, hfix])
    exact (by decide : (22 : Fin 24) ≠ 23) h2223
  · intro hx
    obtain ⟨g, hg⟩ := second_orbit_stabilizer_witness x hx
    exact ⟨g, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg⟩

theorem stab23_orbit_22_ncard :
    (MulAction.orbit (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24)).ncard = 23 := by
  rw [stab23_orbit_22_eq]
  have hset : ({x : Fin 24 | x ≠ 23} : Set (Fin 24)) = ({23} : Set (Fin 24))ᶜ := by
    ext x
    simp
  rw [hset, Set.ncard_compl, Set.ncard_singleton]
  simp

/-! ## Level 3: the stabilizer of `23,22` moving `0` -/

def stab2322Element (x : Fin 24) (hx23 : x ≠ 23) (hx22 : x ≠ 22) :
    MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24) :=
  let g0 : MulAction.stabilizer M24 (23 : Fin 24) :=
    ⟨Word.toM24 (levelThreeWord x), by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (levelThreeWord x)) (23 : Fin 24) = 23
      exact levelThreeWord_fixes_23_all x hx23 hx22⟩
  ⟨g0, by
    rw [MulAction.mem_stabilizer_iff]
    change (Word.eval (levelThreeWord x)) (22 : Fin 24) = 22
    exact levelThreeWord_fixes_22_all x hx23 hx22⟩

theorem third_orbit_stabilizer_witness (x : Fin 24) (hx23 : x ≠ 23) (hx22 : x ≠ 22) :
    ∃ g : MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24),
      g.1.1.1 (0 : Fin 24) = x :=
  ⟨stab2322Element x hx23 hx22, by
    change (Word.eval (levelThreeWord x)) (0 : Fin 24) = x
    exact levelThreeWord_maps_0_all x hx23 hx22⟩

theorem stab2322_orbit_zero_eq :
    MulAction.orbit
        (MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24))
        (0 : Fin 24) =
      {x : Fin 24 | x ≠ 23 ∧ x ≠ 22} := by
  ext x
  constructor
  · rintro ⟨g, hg⟩
    constructor
    · intro hx23
      have hfix23 : g.1.1.1 (23 : Fin 24) = 23 := by
        have h := (MulAction.mem_stabilizer_iff.mp g.1.2)
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h
      have hmap : g.1.1.1 (0 : Fin 24) = 23 := by
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx23] using hg
      have h023 : (0 : Fin 24) = 23 := g.1.1.1.injective (by rw [hmap, hfix23])
      exact (by decide : (0 : Fin 24) ≠ 23) h023
    · intro hx22
      have hfix22 : g.1.1.1 (22 : Fin 24) = 22 := by
        have h := (MulAction.mem_stabilizer_iff.mp g.2)
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h
      have hmap : g.1.1.1 (0 : Fin 24) = 22 := by
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx22] using hg
      have h022 : (0 : Fin 24) = 22 := g.1.1.1.injective (by rw [hmap, hfix22])
      exact (by decide : (0 : Fin 24) ≠ 22) h022
  · rintro ⟨hx23, hx22⟩
    obtain ⟨g, hg⟩ := third_orbit_stabilizer_witness x hx23 hx22
    exact ⟨g, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg⟩

theorem stab2322_orbit_zero_ncard :
    (MulAction.orbit
        (MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24))
        (0 : Fin 24)).ncard = 22 := by
  rw [stab2322_orbit_zero_eq]
  have hset : ({x : Fin 24 | x ≠ 23 ∧ x ≠ 22} : Set (Fin 24)) =
      ↑(({23, 22} : Finset (Fin 24))ᶜ) := by
    ext x
    simp only [Set.mem_setOf_eq, Finset.coe_compl, Set.mem_compl_iff,
      Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton, not_or, ne_eq]
  rw [hset, Set.ncard_coe_finset]
  decide

/-! ## Level 4: the stabilizer of `23,22,0` moving `1` -/

def stab23220Element (x : Fin 24) (hx23 : x ≠ 23) (hx22 : x ≠ 22) (hx0 : x ≠ 0) :
    MulAction.stabilizer
      (MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24))
      (0 : Fin 24) :=
  let g0 : MulAction.stabilizer M24 (23 : Fin 24) :=
    ⟨Word.toM24 (levelFourWord x), by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (levelFourWord x)) (23 : Fin 24) = 23
      exact levelFourWord_fixes_23_all x hx23 hx22 hx0⟩
  let g1 : MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24) :=
    ⟨g0, by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (levelFourWord x)) (22 : Fin 24) = 22
      exact levelFourWord_fixes_22_all x hx23 hx22 hx0⟩
  ⟨g1, by
    rw [MulAction.mem_stabilizer_iff]
    change (Word.eval (levelFourWord x)) (0 : Fin 24) = 0
    exact levelFourWord_fixes_0_all x hx23 hx22 hx0⟩

theorem fourth_orbit_stabilizer_witness (x : Fin 24)
    (hx23 : x ≠ 23) (hx22 : x ≠ 22) (hx0 : x ≠ 0) :
    ∃ g : MulAction.stabilizer
        (MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24))
        (0 : Fin 24),
      g.1.1.1.1 (1 : Fin 24) = x :=
  ⟨stab23220Element x hx23 hx22 hx0, by
    change (Word.eval (levelFourWord x)) (1 : Fin 24) = x
    exact levelFourWord_maps_1_all x hx23 hx22 hx0⟩

theorem stab23220_orbit_one_eq :
    MulAction.orbit
        (MulAction.stabilizer
          (MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24))
          (0 : Fin 24))
        (1 : Fin 24) =
      {x : Fin 24 | x ≠ 23 ∧ x ≠ 22 ∧ x ≠ 0} := by
  ext x
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨?_, ?_, ?_⟩
    · intro hx23
      have hfix23 : g.1.1.1.1 (23 : Fin 24) = 23 := by
        have h := (MulAction.mem_stabilizer_iff.mp g.1.1.2)
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h
      have hmap : g.1.1.1.1 (1 : Fin 24) = 23 := by
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx23] using hg
      have h123 : (1 : Fin 24) = 23 := g.1.1.1.1.injective (by rw [hmap, hfix23])
      exact (by decide : (1 : Fin 24) ≠ 23) h123
    · intro hx22
      have hfix22 : g.1.1.1.1 (22 : Fin 24) = 22 := by
        have h := (MulAction.mem_stabilizer_iff.mp g.1.2)
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h
      have hmap : g.1.1.1.1 (1 : Fin 24) = 22 := by
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx22] using hg
      have h122 : (1 : Fin 24) = 22 := g.1.1.1.1.injective (by rw [hmap, hfix22])
      exact (by decide : (1 : Fin 24) ≠ 22) h122
    · intro hx0
      have hfix0 : g.1.1.1.1 (0 : Fin 24) = 0 := by
        have h := (MulAction.mem_stabilizer_iff.mp g.2)
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h
      have hmap : g.1.1.1.1 (1 : Fin 24) = 0 := by
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx0] using hg
      have h10 : (1 : Fin 24) = 0 := g.1.1.1.1.injective (by rw [hmap, hfix0])
      exact (by decide : (1 : Fin 24) ≠ 0) h10
  · rintro ⟨hx23, hx22, hx0⟩
    obtain ⟨g, hg⟩ := fourth_orbit_stabilizer_witness x hx23 hx22 hx0
    exact ⟨g, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg⟩

theorem stab23220_orbit_one_ncard :
    (MulAction.orbit
        (MulAction.stabilizer
          (MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24))
          (0 : Fin 24))
        (1 : Fin 24)).ncard = 21 := by
  rw [stab23220_orbit_one_eq]
  have hset : ({x : Fin 24 | x ≠ 23 ∧ x ≠ 22 ∧ x ≠ 0} : Set (Fin 24)) =
      ↑(({23, 22, 0} : Finset (Fin 24))ᶜ) := by
    ext x
    simp only [Set.mem_setOf_eq, Finset.coe_compl, Set.mem_compl_iff,
      Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton, not_or, ne_eq]
  rw [hset, Set.ncard_coe_finset]
  decide

/-! ## Level 5: the stabilizer of `23,22,0,1` moving `2` -/

def stab232201Element (x : Fin 24)
    (hx23 : x ≠ 23) (hx22 : x ≠ 22) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    MulAction.stabilizer
      (MulAction.stabilizer
        (MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24))
        (0 : Fin 24))
      (1 : Fin 24) :=
  let g0 : MulAction.stabilizer M24 (23 : Fin 24) :=
    ⟨Word.toM24 (levelFiveWord x), by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (levelFiveWord x)) (23 : Fin 24) = 23
      exact levelFiveWord_fixes_23_all x hx23 hx22 hx0 hx1⟩
  let g1 : MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24) :=
    ⟨g0, by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (levelFiveWord x)) (22 : Fin 24) = 22
      exact levelFiveWord_fixes_22_all x hx23 hx22 hx0 hx1⟩
  let g2 : MulAction.stabilizer
      (MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24))
      (0 : Fin 24) :=
    ⟨g1, by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (levelFiveWord x)) (0 : Fin 24) = 0
      exact levelFiveWord_fixes_0_all x hx23 hx22 hx0 hx1⟩
  ⟨g2, by
    rw [MulAction.mem_stabilizer_iff]
    change (Word.eval (levelFiveWord x)) (1 : Fin 24) = 1
    exact levelFiveWord_fixes_1_all x hx23 hx22 hx0 hx1⟩

theorem fifth_orbit_stabilizer_witness (x : Fin 24)
    (hx23 : x ≠ 23) (hx22 : x ≠ 22) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    ∃ g : MulAction.stabilizer
        (MulAction.stabilizer
          (MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24))
          (0 : Fin 24))
        (1 : Fin 24),
      g.1.1.1.1.1 (2 : Fin 24) = x :=
  ⟨stab232201Element x hx23 hx22 hx0 hx1, by
    change (Word.eval (levelFiveWord x)) (2 : Fin 24) = x
    exact levelFiveWord_maps_2_all x hx23 hx22 hx0 hx1⟩

theorem stab232201_orbit_two_eq :
    MulAction.orbit
        (MulAction.stabilizer
          (MulAction.stabilizer
            (MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24))
            (0 : Fin 24))
          (1 : Fin 24))
        (2 : Fin 24) =
      {x : Fin 24 | x ≠ 23 ∧ x ≠ 22 ∧ x ≠ 0 ∧ x ≠ 1} := by
  ext x
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hx23
      have hfix23 : g.1.1.1.1.1 (23 : Fin 24) = 23 := by
        have h := (MulAction.mem_stabilizer_iff.mp g.1.1.1.2)
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h
      have hmap : g.1.1.1.1.1 (2 : Fin 24) = 23 := by
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx23] using hg
      have h223 : (2 : Fin 24) = 23 := g.1.1.1.1.1.injective (by rw [hmap, hfix23])
      exact (by decide : (2 : Fin 24) ≠ 23) h223
    · intro hx22
      have hfix22 : g.1.1.1.1.1 (22 : Fin 24) = 22 := by
        have h := (MulAction.mem_stabilizer_iff.mp g.1.1.2)
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h
      have hmap : g.1.1.1.1.1 (2 : Fin 24) = 22 := by
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx22] using hg
      have h222 : (2 : Fin 24) = 22 := g.1.1.1.1.1.injective (by rw [hmap, hfix22])
      exact (by decide : (2 : Fin 24) ≠ 22) h222
    · intro hx0
      have hfix0 : g.1.1.1.1.1 (0 : Fin 24) = 0 := by
        have h := (MulAction.mem_stabilizer_iff.mp g.1.2)
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h
      have hmap : g.1.1.1.1.1 (2 : Fin 24) = 0 := by
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx0] using hg
      have h20 : (2 : Fin 24) = 0 := g.1.1.1.1.1.injective (by rw [hmap, hfix0])
      exact (by decide : (2 : Fin 24) ≠ 0) h20
    · intro hx1
      have hfix1 : g.1.1.1.1.1 (1 : Fin 24) = 1 := by
        have h := (MulAction.mem_stabilizer_iff.mp g.2)
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h
      have hmap : g.1.1.1.1.1 (2 : Fin 24) = 1 := by
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx1] using hg
      have h21 : (2 : Fin 24) = 1 := g.1.1.1.1.1.injective (by rw [hmap, hfix1])
      exact (by decide : (2 : Fin 24) ≠ 1) h21
  · rintro ⟨hx23, hx22, hx0, hx1⟩
    obtain ⟨g, hg⟩ := fifth_orbit_stabilizer_witness x hx23 hx22 hx0 hx1
    exact ⟨g, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg⟩

theorem stab232201_orbit_two_ncard :
    (MulAction.orbit
        (MulAction.stabilizer
          (MulAction.stabilizer
            (MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24))
            (0 : Fin 24))
          (1 : Fin 24))
        (2 : Fin 24)).ncard = 20 := by
  rw [stab232201_orbit_two_eq]
  have hset : ({x : Fin 24 | x ≠ 23 ∧ x ≠ 22 ∧ x ≠ 0 ∧ x ≠ 1} : Set (Fin 24)) =
      ↑(({23, 22, 0, 1} : Finset (Fin 24))ᶜ) := by
    ext x
    simp only [Set.mem_setOf_eq, Finset.coe_compl, Set.mem_compl_iff,
      Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton, not_or, ne_eq]
  rw [hset, Set.ncard_coe_finset]
  decide

/-! ## Level 6: the stabilizer of `23,22,0,1,2` moving `5` outside the block `B0` -/

def levelSixElement (x : Fin 24) (hx : x ∈ blockB0ᶜ) :
    MulAction.stabilizer
      (MulAction.stabilizer
        (MulAction.stabilizer
          (MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24))
          (0 : Fin 24))
        (1 : Fin 24))
      (2 : Fin 24) :=
  let g0 : MulAction.stabilizer M24 (23 : Fin 24) :=
    ⟨Word.toM24 (levelSixWord x), by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (levelSixWord x)) (23 : Fin 24) = 23
      exact levelSixWord_fixes_23_all x hx⟩
  let g1 : MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24) :=
    ⟨g0, by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (levelSixWord x)) (22 : Fin 24) = 22
      exact levelSixWord_fixes_22_all x hx⟩
  let g2 : MulAction.stabilizer
      (MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24))
      (0 : Fin 24) :=
    ⟨g1, by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (levelSixWord x)) (0 : Fin 24) = 0
      exact levelSixWord_fixes_0_all x hx⟩
  let g3 : MulAction.stabilizer
      (MulAction.stabilizer
        (MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24))
        (0 : Fin 24))
      (1 : Fin 24) :=
    ⟨g2, by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (levelSixWord x)) (1 : Fin 24) = 1
      exact levelSixWord_fixes_1_all x hx⟩
  ⟨g3, by
    rw [MulAction.mem_stabilizer_iff]
    change (Word.eval (levelSixWord x)) (2 : Fin 24) = 2
    exact levelSixWord_fixes_2_all x hx⟩

theorem sixth_orbit_stabilizer_witness (x : Fin 24) (hx : x ∈ blockB0ᶜ) :
    ∃ g : MulAction.stabilizer
        (MulAction.stabilizer
          (MulAction.stabilizer
            (MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24))
            (0 : Fin 24))
          (1 : Fin 24))
        (2 : Fin 24),
      g.1.1.1.1.1.1 (5 : Fin 24) = x :=
  ⟨levelSixElement x hx, by
    change (Word.eval (levelSixWord x)) (5 : Fin 24) = x
    exact levelSixWord_maps_5_all x hx⟩

/-- An element fixing `23,22,0,1,2` preserves the block `B0` setwise. -/
theorem blockMap_B0_of_fixes (π : Perm24)
    (hpres : ∀ B ∈ octadList, blockMap π B ∈ octads)
    (h23 : π 23 = 23) (h22 : π 22 = 22) (h0 : π 0 = 0) (h1 : π 1 = 1)
    (h2 : π 2 = 2) :
    blockMap π blockB0 = blockB0 :=
  blockMap_eq_of_five π hpres octadAt_zero (by decide) (by decide) (by decide)
    (by decide) (by decide) h0 h1 h2 h22 h23 unique_block_01_2_22_23
    octadAt_zero

theorem stab2322012_orbit_five_eq :
    MulAction.orbit
        (MulAction.stabilizer
          (MulAction.stabilizer
            (MulAction.stabilizer
              (MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24))
              (0 : Fin 24))
            (1 : Fin 24))
          (2 : Fin 24))
        (5 : Fin 24) = ↑(blockB0ᶜ) := by
  ext x
  constructor
  · rintro ⟨g, hg⟩
    have hfix23 : g.1.1.1.1.1.1 (23 : Fin 24) = 23 := by
      have h := (MulAction.mem_stabilizer_iff.mp g.1.1.1.1.2)
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h
    have hfix22 : g.1.1.1.1.1.1 (22 : Fin 24) = 22 := by
      have h := (MulAction.mem_stabilizer_iff.mp g.1.1.1.2)
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h
    have hfix0 : g.1.1.1.1.1.1 (0 : Fin 24) = 0 := by
      have h := (MulAction.mem_stabilizer_iff.mp g.1.1.2)
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h
    have hfix1 : g.1.1.1.1.1.1 (1 : Fin 24) = 1 := by
      have h := (MulAction.mem_stabilizer_iff.mp g.1.2)
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h
    have hfix2 : g.1.1.1.1.1.1 (2 : Fin 24) = 2 := by
      have h := (MulAction.mem_stabilizer_iff.mp g.2)
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h
    have hmap : g.1.1.1.1.1.1 (5 : Fin 24) = x := by
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg
    have hB0 : blockMap g.1.1.1.1.1.1 blockB0 = blockB0 :=
      blockMap_B0_of_fixes g.1.1.1.1.1.1 (M24_preserves_octads g.1.1.1.1.1).1
        hfix23 hfix22 hfix0 hfix1 hfix2
    rw [Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe]
    intro hxB0
    rw [← hB0] at hxB0
    obtain ⟨w, hwB0, hw⟩ := Finset.mem_image.mp hxB0
    have hw5 : w = 5 := g.1.1.1.1.1.1.injective (by rw [hw, hmap])
    rw [hw5] at hwB0
    exact (by decide : (5 : Fin 24) ∉ blockB0) hwB0
  · intro hx
    have hxc : x ∈ blockB0ᶜ := Finset.mem_coe.mp hx
    obtain ⟨g, hg⟩ := sixth_orbit_stabilizer_witness x hxc
    exact ⟨g, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg⟩

theorem stab2322012_orbit_five_ncard :
    (MulAction.orbit
        (MulAction.stabilizer
          (MulAction.stabilizer
            (MulAction.stabilizer
              (MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24))
              (0 : Fin 24))
            (1 : Fin 24))
          (2 : Fin 24))
        (5 : Fin 24)).ncard = 16 := by
  rw [stab2322012_orbit_five_eq, Set.ncard_coe_finset]
  decide

/-! ## Level 7: the stabilizer of `23,22,0,1,2,5` moving `3` inside the block `B0` -/

set_option maxHeartbeats 1600000 in
-- The membership pin certificate is intentionally checked by computation.
set_option maxRecDepth 400000 in
/-- Inside `B0`, the points other than the fixed `23,22,0,1,2` are
`3`, `4`, `21`. -/
theorem pin_three :
    ∀ v : Fin 24, v ∈ blockB0 → v ≠ 23 → v ≠ 22 → v ≠ 0 → v ≠ 1 → v ≠ 2 →
      v ∈ ({3, 4, 21} : Finset (Fin 24)) := by
  decide

theorem mem_targets_iff :
    ∀ x : Fin 24, x ∈ ({3, 4, 21} : Finset (Fin 24)) →
      (x = 3 ∨ x = 4 ∨ x = 21) := by
  decide

def levelSevenElement (x : Fin 24) (hx : x = 3 ∨ x = 4 ∨ x = 21) :
    MulAction.stabilizer
      (MulAction.stabilizer
        (MulAction.stabilizer
          (MulAction.stabilizer
            (MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24))
            (0 : Fin 24))
          (1 : Fin 24))
        (2 : Fin 24))
      (5 : Fin 24) :=
  let g0 : MulAction.stabilizer M24 (23 : Fin 24) :=
    ⟨Word.toM24 (levelSevenWord x), by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (levelSevenWord x)) (23 : Fin 24) = 23
      exact levelSevenWord_fixes_23_all x hx⟩
  let g1 : MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24) :=
    ⟨g0, by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (levelSevenWord x)) (22 : Fin 24) = 22
      exact levelSevenWord_fixes_22_all x hx⟩
  let g2 : MulAction.stabilizer
      (MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24))
      (0 : Fin 24) :=
    ⟨g1, by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (levelSevenWord x)) (0 : Fin 24) = 0
      exact levelSevenWord_fixes_0_all x hx⟩
  let g3 : MulAction.stabilizer
      (MulAction.stabilizer
        (MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24))
        (0 : Fin 24))
      (1 : Fin 24) :=
    ⟨g2, by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (levelSevenWord x)) (1 : Fin 24) = 1
      exact levelSevenWord_fixes_1_all x hx⟩
  let g4 : MulAction.stabilizer
      (MulAction.stabilizer
        (MulAction.stabilizer
          (MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24))
          (0 : Fin 24))
        (1 : Fin 24))
      (2 : Fin 24) :=
    ⟨g3, by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (levelSevenWord x)) (2 : Fin 24) = 2
      exact levelSevenWord_fixes_2_all x hx⟩
  ⟨g4, by
    rw [MulAction.mem_stabilizer_iff]
    change (Word.eval (levelSevenWord x)) (5 : Fin 24) = 5
    exact levelSevenWord_fixes_5_all x hx⟩

theorem seventh_orbit_stabilizer_witness (x : Fin 24)
    (hx : x = 3 ∨ x = 4 ∨ x = 21) :
    ∃ g : MulAction.stabilizer
        (MulAction.stabilizer
          (MulAction.stabilizer
            (MulAction.stabilizer
              (MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24))
              (0 : Fin 24))
            (1 : Fin 24))
          (2 : Fin 24))
        (5 : Fin 24),
      g.1.1.1.1.1.1.1 (3 : Fin 24) = x :=
  ⟨levelSevenElement x hx, by
    change (Word.eval (levelSevenWord x)) (3 : Fin 24) = x
    exact levelSevenWord_maps_3_all x hx⟩

set_option maxHeartbeats 3200000 in
theorem stab23220125_orbit_three_eq :
    MulAction.orbit
        (MulAction.stabilizer
          (MulAction.stabilizer
            (MulAction.stabilizer
              (MulAction.stabilizer
                (MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24))
                (0 : Fin 24))
              (1 : Fin 24))
            (2 : Fin 24))
          (5 : Fin 24))
        (3 : Fin 24) = ↑({3, 4, 21} : Finset (Fin 24)) := by
  ext x
  constructor
  · rintro ⟨g, hg⟩
    have hfix23 : g.1.1.1.1.1.1.1 (23 : Fin 24) = 23 := by
      have h := (MulAction.mem_stabilizer_iff.mp g.1.1.1.1.1.2)
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h
    have hfix22 : g.1.1.1.1.1.1.1 (22 : Fin 24) = 22 := by
      have h := (MulAction.mem_stabilizer_iff.mp g.1.1.1.1.2)
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h
    have hfix0 : g.1.1.1.1.1.1.1 (0 : Fin 24) = 0 := by
      have h := (MulAction.mem_stabilizer_iff.mp g.1.1.1.2)
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h
    have hfix1 : g.1.1.1.1.1.1.1 (1 : Fin 24) = 1 := by
      have h := (MulAction.mem_stabilizer_iff.mp g.1.1.2)
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h
    have hfix2 : g.1.1.1.1.1.1.1 (2 : Fin 24) = 2 := by
      have h := (MulAction.mem_stabilizer_iff.mp g.1.2)
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h
    have hmap : g.1.1.1.1.1.1.1 (3 : Fin 24) = x := by
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg
    have hB0 : blockMap g.1.1.1.1.1.1.1 blockB0 = blockB0 :=
      blockMap_B0_of_fixes g.1.1.1.1.1.1.1 (M24_preserves_octads g.1.1.1.1.1.1).1
        hfix23 hfix22 hfix0 hfix1 hfix2
    have hmem : x ∈ blockB0 := by
      rw [← hmap]
      exact mem_of_blockMap_eq g.1.1.1.1.1.1.1 hB0 (by decide)
    rw [Finset.mem_coe]
    refine pin_three x hmem ?_ ?_ ?_ ?_ ?_
    · rw [← hmap]
      exact ne_of_value g.1.1.1.1.1.1.1 hfix23 (by decide)
    · rw [← hmap]
      exact ne_of_value g.1.1.1.1.1.1.1 hfix22 (by decide)
    · rw [← hmap]
      exact ne_of_value g.1.1.1.1.1.1.1 hfix0 (by decide)
    · rw [← hmap]
      exact ne_of_value g.1.1.1.1.1.1.1 hfix1 (by decide)
    · rw [← hmap]
      exact ne_of_value g.1.1.1.1.1.1.1 hfix2 (by decide)
  · intro hx
    have hxor := mem_targets_iff x (Finset.mem_coe.mp hx)
    obtain ⟨g, hg⟩ := seventh_orbit_stabilizer_witness x hxor
    exact ⟨g, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg⟩

set_option maxHeartbeats 3200000 in
theorem stab23220125_orbit_three_ncard :
    (MulAction.orbit
        (MulAction.stabilizer
          (MulAction.stabilizer
            (MulAction.stabilizer
              (MulAction.stabilizer
                (MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24))
                (0 : Fin 24))
              (1 : Fin 24))
            (2 : Fin 24))
          (5 : Fin 24))
        (3 : Fin 24)).ncard = 3 := by
  rw [stab23220125_orbit_three_eq, Set.ncard_coe_finset]
  decide

end ChainOrbits
end M24Certificates
end CFSG.Certificates.Mathieu24
