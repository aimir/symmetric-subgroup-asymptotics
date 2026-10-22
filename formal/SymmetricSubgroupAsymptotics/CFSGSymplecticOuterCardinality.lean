import SymmetricSubgroupAsymptotics.CFSGSymplecticRootFamilyOuterBound
import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryFamilyStabilizer
import SymmetricSubgroupAsymptotics.CFSGSymplecticMinimumIndexLower

/-! Both characteristic branches bound the outer group of the SAME
original projective symplectic model: 2 field automorphisms in odd
characteristic, and 3 in characteristic two. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticPointRootLabels
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry CFSGSymplecticUnipotent
open PrimitiveSocleRawStructure CFSGNormalizerCenterAtoms
variable {K : Type} [Field K] [Finite K]

theorem binary_outer_card_le [CharP K 2] (r : ℕ) (hr : 0 < r)
    [IsSimpleGroup (elementaryProjective K (r + 1))] :
    Nat.card (Outer (elementaryProjective K (r + 1))) ≤ 3 * Nat.card (K ≃+* K) := by
  let S := naturalRootFamilyStabilizer (K := K) r hr
  have hinner (g : elementaryProjective K (r + 1)) : MulAut.conj g ∈ S := by
    apply (mem_familyStabilizer _ _).mpr
    exact innerFamily_conjugate _ g
  have h := family_outer_card_le r hr S hinner
    (naturalRootFamilyStabilizer_point_stable r hr) 3
    (binaryChar_naturalRootFamilyStabilizer_index_le_three r hr)
  have hc : Nat.card (Subgroup.center (elementaryRootGroup K (r + 1))) = 1 := by
    rw [center_eq_bot_of_char_two K r]
    simp
  simpa only [hc, mul_one] using h

theorem outer_card_le_three_ringAut (p r : ℕ) [Fact p.Prime] [CharP K p]
    (hr : 0 < r) [IsSimpleGroup (elementaryProjective K (r + 1))] :
    Nat.card (Outer (elementaryProjective K (r + 1))) ≤ 3 * Nat.card (K ≃+* K) := by
  by_cases hp : p = 2
  · letI : CharP K 2 := by rw [← hp]; infer_instance
    exact binary_outer_card_le r hr
  · have htwo : (2 : K) ≠ 0 := by
      intro h
      have hd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp h
      exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hd)
    exact (odd_outer_card_le p r hr htwo).trans (Nat.mul_le_mul_right _ (by decide : 2 ≤ 3))

end SymmetricSubgroupAsymptotics.CFSGSymplecticPointRootLabels

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGSymplecticSerreMatrices PrimitiveSocleRawStructure

theorem typeC_outer_card_le (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.C r q)] :
    Nat.card (Outer (CFSG.Models.C r q)) ≤ 3 * Nat.card (q.Field ≃+* q.Field) := by
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s + 2 := ⟨r - 2, by omega⟩
  let e : CFSG.Models.C (s + 2) q ≃* elementaryProjective q.Field (s + 2) :=
    serreProjectiveEquivElementaryProjective q.Field (s + 1)
  letI : IsSimpleGroup (elementaryProjective q.Field (s + 2)) := e.symm.isSimpleGroup
  rw [outer_card_congr e]
  exact CFSGSymplecticPointRootLabels.outer_card_le_three_ringAut q.prime (s + 1) (by omega)

end SymmetricSubgroupAsymptotics.CFSGReduction
