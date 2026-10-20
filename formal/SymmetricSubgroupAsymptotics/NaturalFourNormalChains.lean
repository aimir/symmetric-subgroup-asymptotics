import SymmetricSubgroupAsymptotics.NaturalA4ScalarFourHead
import SymmetricSubgroupAsymptotics.Non2PreE7NaturalS4Group
import SymmetricSubgroupAsymptotics.OddPrimeDihedralNormalChain
import SymmetricSubgroupAsymptotics.NormalChainSocleGenerators
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Closure

/-! Normal chains for the literal natural A4 and S4. The S4 argument uses
its actual pairing map to S3 and the previously proved minimal,
self-centralizing Klein kernel. The six-point dihedral formula checks
only the multiplication identity of a displayed map; no normal-subgroup
or generated-group enumeration is used. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.NaturalFourNormalChains

theorem alternating_normal_total
    (A B : Subgroup (alternatingGroup (Fin 4))) (hA : A.Normal) (hB : B.Normal) :
    A ≤ B ∨ B ≤ A := by
  rcases NaturalA4ScalarFourHead.normal_subgroup_trichotomy A hA with h | h | h
  · left; rw [h]; exact bot_le
  · rcases NaturalA4ScalarFourHead.normal_subgroup_trichotomy B hB with k | k | k
    · right; rw [k]; exact bot_le
    · left; rw [h,k]
    · left; rw [k]; exact le_top
  · right; rw [h]; exact le_top

def dihedralThree : DihedralGroup 3 →* Equiv.Perm (Fin 3) where
  toFun
    | .r i => finRotate 3 ^ i.val
    | .sr i => Equiv.swap 0 1 * finRotate 3 ^ i.val
  map_one' := by decide +kernel
  map_mul' := by
    intro x y
    revert x y
    decide +kernel

theorem dihedralThree_surjective : Function.Surjective dihedralThree := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  have hgen : Subgroup.closure
      ({finRotate 3, Equiv.swap (0 : Fin 3) 1} : Set (Equiv.Perm (Fin 3))) = ⊤ := by
    simpa only [show finRotate 3 (0 : Fin 3) = 1 from rfl] using
      Equiv.Perm.closure_cycle_adjacent_swap
        (isCycle_finRotate_of_le (by decide : 2 ≤ 3))
        (support_finRotate_of_le (by decide : 2 ≤ 3)) (0 : Fin 3)
  rw [← hgen]
  apply (Subgroup.closure_le _).mpr
  intro x hx
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact ⟨DihedralGroup.r 1, by decide +kernel⟩
  · exact ⟨DihedralGroup.sr 0, by decide +kernel⟩

theorem symmetric_three_normal_total
    (A B : Subgroup (Equiv.Perm (Fin 3))) (hA : A.Normal) (hB : B.Normal) :
    A ≤ B ∨ B ≤ A :=
  normalSubgroups_total_of_surjective dihedralThree dihedralThree_surjective
    (OddPrimeDihedralNormalChain.normal_total (p := 3) (by decide)) A B hA hB

theorem symmetric_normal_total
    (A B : Subgroup (Equiv.Perm (Fin 4))) (hA : A.Normal) (hB : B.Normal) :
    A ≤ B ∨ B ≤ A := by
  classical
  by_cases hAb : A = ⊥
  · left; rw [hAb]; exact bot_le
  by_cases hBb : B = ⊥
  · right; rw [hBb]; exact bot_le
  letI := hA
  letI := hB
  have hkerA : NaturalS4.pairing.ker ≤ A := by
    rw [NaturalS4.ker_pairing]
    exact le_of_minimal_selfCentralizing NaturalS4.klein
      NaturalS4.klein_minimal NaturalS4.klein_selfCentralizing A hAb
  have hkerB : NaturalS4.pairing.ker ≤ B := by
    rw [NaturalS4.ker_pairing]
    exact le_of_minimal_selfCentralizing NaturalS4.klein
      NaturalS4.klein_minimal NaturalS4.klein_selfCentralizing B hBb
  rcases symmetric_three_normal_total
      (A.map NaturalS4.pairing) (B.map NaturalS4.pairing)
      (hA.map _ NaturalS4.pairing_surjective)
      (hB.map _ NaturalS4.pairing_surjective) with h | h
  · left
    calc
      A = (A.map NaturalS4.pairing).comap NaturalS4.pairing :=
        (Subgroup.comap_map_eq_self hkerA).symm
      _ ≤ (B.map NaturalS4.pairing).comap NaturalS4.pairing := Subgroup.comap_mono h
      _ = B := Subgroup.comap_map_eq_self hkerB
  · right
    calc
      B = (B.map NaturalS4.pairing).comap NaturalS4.pairing :=
        (Subgroup.comap_map_eq_self hkerB).symm
      _ ≤ (A.map NaturalS4.pairing).comap NaturalS4.pairing := Subgroup.comap_mono h
      _ = A := Subgroup.comap_map_eq_self hkerA

end SymmetricSubgroupAsymptotics.NaturalFourNormalChains

end
