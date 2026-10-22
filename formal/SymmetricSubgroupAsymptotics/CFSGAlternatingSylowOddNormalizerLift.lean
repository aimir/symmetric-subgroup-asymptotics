import SymmetricSubgroupAsymptotics.CFSGDihedralTwoGroupWords
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Sylow

/-! An actual odd normalizing involution extends an alternating Sylow
two-subgroup to a symmetric Sylow subgroup inside the same displayed
ambient subgroup. Maximality is proved by the literal sign kernel. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingSylowOddNormalizerLift
open Equiv Equiv.Perm

theorem exists_symmetricSylow_between
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Sylow 2 (alternatingGroup X)) (S : Subgroup (Perm X))
    (hPS : (P : Subgroup (alternatingGroup X)).map (alternatingGroup X).subtype ≤ S)
    (t : Perm X) (htS : t ∈ S) (htodd : t ∉ alternatingGroup X) (ht2 : t ^ 2 = 1)
    (htN : t ∈ Subgroup.normalizer
      ((P : Subgroup (alternatingGroup X)).map (alternatingGroup X).subtype : Set (Perm X))) :
    ∃ Q : Sylow 2 (Perm X),
      (P : Subgroup (alternatingGroup X)).map (alternatingGroup X).subtype ≤ Q ∧ Q ≤ S := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A := alternatingGroup X
  let Pi := (P : Subgroup A).map A.subtype
  let H := Subgroup.zpowers t ⊔ Pi
  have hPiH : Pi ≤ H := le_sup_right
  have htH : t ∈ H := (show Subgroup.zpowers t ≤ H from le_sup_left) (Subgroup.mem_zpowers t)
  have hPi : IsPGroup 2 Pi := P.isPGroup'.map A.subtype
  have htP : IsPGroup 2 (Subgroup.zpowers t) :=
    CFSGDihedralTwoGroupWords.zpowers_isPGroup_of_pow t 1 (by simpa using ht2)
  have hH : IsPGroup 2 H := htP.to_sup_of_normal_right' hPi (Subgroup.zpowers_le.mpr htN)
  obtain ⟨R, hHR⟩ := hH.exists_le_sylow
  have hPR : (P : Subgroup A) ≤ (R : Subgroup (Perm X)).comap A.subtype := by
    intro g hg
    exact hHR (hPiH ⟨g, hg, rfl⟩)
  have hReven : (R : Subgroup (Perm X)).comap A.subtype = (P : Subgroup A) :=
    P.is_maximal' (R.isPGroup'.comap_of_injective A.subtype A.subtype_injective) hPR
  have even_mem (r : Perm X) (hr : r ∈ R) (hre : r ∈ A) : r ∈ H := by
    have hp : (⟨r, hre⟩ : A) ∈ (R : Subgroup (Perm X)).comap A.subtype := hr
    rw [hReven] at hp
    exact hPiH ⟨⟨r, hre⟩, hp, rfl⟩
  have htSign : sign t = -1 := by
    rcases Int.units_eq_one_or (sign t) with h | h
    · exact False.elim (htodd (mem_alternatingGroup.mpr h))
    · exact h
  have hRH : (R : Subgroup (Perm X)) ≤ H := by
    intro r hr
    by_cases hre : r ∈ A
    · exact even_mem r hr hre
    · have hrSign : sign r = -1 := by
        rcases Int.units_eq_one_or (sign r) with h | h
        · exact False.elim (hre (mem_alternatingGroup.mpr h))
        · exact h
      have hrtA : r * t ∈ A := by
        apply mem_alternatingGroup.mpr
        rw [map_mul, hrSign, htSign]
        norm_num
      have hm := H.mul_mem (even_mem (r * t) (R.mul_mem hr (hHR htH)) hrtA) htH
      simpa only [mul_assoc, ← pow_two, ht2, mul_one] using hm
  refine ⟨R, hPiH.trans hHR, hRH.trans ?_⟩
  exact sup_le (Subgroup.zpowers_le.mpr htS) hPS

end SymmetricSubgroupAsymptotics.CFSGAlternatingSylowOddNormalizerLift
