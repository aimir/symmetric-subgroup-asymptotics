import SymmetricSubgroupAsymptotics.BinaryPairRankTwoTranslationChart
import SymmetricSubgroupAsymptotics.OriginalKernelCenterInclusion

/-! The nonzero-parity owner on the same original normal quotient.

The original normal is first recovered by the checked commutator and
normal-center argument. The resulting equality of subgroups transports
centrality back to U/N. Its exact section chart then identifies the
complete central omega with the original two-dimensional fixed space.
The zero-parity branch is not covered by this character entry.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) (N : Subgroup U) [N.Normal]
    [Finite X] [Finite I] [MulAction.IsPretransitive F.top.range I]
    (hU : IsPGroup 2 U) (hI : Nat.card I=8)
    (hres : F.EightPairRankTwoResidual N)
    (hlarge : 8<Nat.card F.top.range)
    (hparity : ∃ h,F.rankTwoTranslationParity N hU hI hres hlarge h≠0)

include hU hI hres hlarge hparity in
/-- Centrality is transported by the proved equality of the original
normal subgroups, not by a claim that central rank decreases in quotients. -/
theorem rankTwo_nonzero_parity_original_center_mem_kernel
    (u : U) (hu : QuotientGroup.mk' N u∈Subgroup.center (U ⧸ N)) : u∈F.top.ker := by
  have hN := F.rankTwo_nonzero_parity_normal_eq N hU hI hres hlarge hparity
  let e : (U ⧸ N) ≃* U ⧸ (N⊓F.top.ker) := QuotientGroup.quotientMulEquivOfEq hN
  have he (v : U) : e (QuotientGroup.mk' N v)=QuotientGroup.mk' (N⊓F.top.ker) v :=
    QuotientGroup.quotientMulEquivOfEq_mk hN v
  apply F.rankTwo_nonzero_parity_center_mem_kernel N hU hI hres hlarge hparity u
  apply Subgroup.mem_center_iff.mpr
  intro q
  obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (N⊓F.top.ker) q
  have hc := congrArg e (Subgroup.mem_center_iff.mp hu (QuotientGroup.mk' N v))
  rw [map_mul,map_mul,he,he] at hc
  exact hc

include hU hI hres hlarge hparity in
/-- The actual section kernel inside the unchanged U/N contains its
whole center. The base representation is not assumed faithful. -/
theorem rankTwo_nonzero_parity_center_le_section_kernel :
    Subgroup.center (U ⧸ N)≤(F.zeroCutBase N).ker := by
  intro q hq
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective N q
  apply MonoidHom.mem_ker.mpr
  rw [F.zeroCutBase_apply]
  exact (QuotientGroup.eq_one_iff _).mpr
    (Subgroup.mem_sup_left
      (F.rankTwo_nonzero_parity_original_center_mem_kernel N hU hI hres hlarge hparity u hq))

include hU hI hres hlarge hparity in
/-- Complete central omega cardinality on the same original quotient. -/
theorem rankTwo_nonzero_parity_centralOmega_card :
    Nat.card (binaryCentralOmega (U ⧸ N))=4 := by
  have hc := (F.sectionModuleChart N).binaryCentralOmega_card_of_center_le
    (F.zeroCutBase_surjective N)
    (F.rankTwo_nonzero_parity_center_le_section_kernel N hU hI hres hlarge hparity)
  change Nat.card (binaryCentralOmega (U ⧸ N))=
    2^Module.finrank (ZMod 2) (F.sectionRepresentation N).invariants at hc
  rw [hres.2.1] at hc
  exact hc

/-- The actual nonzero twist satisfies the new exact character test.
Its normal quotient, degree and complete omega cardinal are original. -/
def rankTwoNonzeroParitySevenCriterion :
    BinarySevenCharacterCriterion (U ⧸ N) (Nat.card X) where
  dimension := 2
  cardinal := F.rankTwo_nonzero_parity_centralOmega_card N hU hI hres hlarge hparity
  gap := by
    rw [F.card_points,hI]
    exact binarySeven_character_gap_of_sixteen_mul_le (2*8) 2 (by decide) (by decide)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
