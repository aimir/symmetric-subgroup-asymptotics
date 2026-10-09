import SymmetricSubgroupAsymptotics.BinaryPairZeroCutExtension
import SymmetricSubgroupAsymptotics.FiniteSurjectiveKernelTransport

/-!
# Quotients of a pair action and a literal model of its top

This is the group-generic form of the same-kernel bridge used by the
degree-two pair catalogues.  It is factored out here because a paired-eight
row applies it twice: first to the sixteen-pair action and then to its
eight-pair top.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryPairFrame

variable {X I G : Type*} [Group G]
  {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I)
  (e : G ≃* F.top.range)

/-- The image of an original normal subgroup, written in the chosen literal
model of the pair top. -/
def literalTopNormal (N : Subgroup U) : Subgroup G :=
  (N.map F.top.rangeRestrict).comap e.toMonoidHom

theorem literalTopNormal_normal (N : Subgroup U) [N.Normal] :
    (F.literalTopNormal e N).Normal := by
  apply Subgroup.Normal.comap
  exact Subgroup.Normal.map inferInstance _
    F.top.rangeRestrict_surjective

/-- The quotient of the original group maps onto the corresponding quotient
of the literal top. -/
noncomputable def literalTopQuotientMap
    (N : Subgroup U) [N.Normal] :
    (U ⟸ N) →* (G ⟸ F.literalTopNormal e N) := by
  let f : U →* (G ⟸ F.literalTopNormal e N) :=
    (QuotientGroup.mk' (F.literalTopNormal e N)).comp
      (e.symm.toMonoidHom.comp F.top.rangeRestrict)
  apply QuotientGroup.lift N f
  intro u hu
  apply MonoidHom.mem_ker.mpr
  apply QuotientGroup.eq_one_iff.mpr
  change e (e.symm (F.top.rangeRestrict u)) ∈
    N.map F.top.rangeRestrict
  rw [e.apply_symm_apply]
  exact ⟨u, hu, rfl⟩

@[simp] theorem literalTopQuotientMap_apply
    (N : Subgroup U) [N.Normal] (u : U) :
    F.literalTopQuotientMap e N (QuotientGroup.mk' N u) =
      QuotientGroup.mk' (F.literalTopNormal e N)
        (e.symm (F.top.rangeRestrict u)) :=
  rfl

theorem literalTopQuotientMap_surjective
    (N : Subgroup U) [N.Normal] :
    Function.Surjective (F.literalTopQuotientMap e N) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    (F.literalTopNormal e N) q
  obtain ⟨u, hu⟩ := F.top.rangeRestrict_surjective (e g)
  refine ⟨QuotientGroup.mk' N u, ?_⟩
  rw [F.literalTopQuotientMap_apply e N u, hu, e.symm_apply_apply]

private theorem literalTop_mem_normal_iff
    (N : Subgroup U) [N.Normal] (u : U) :
    e.symm (F.top.rangeRestrict u) ∈ F.literalTopNormal e N ↔
      u ∈ F.top.ker ⊔ N := by
  change e (e.symm (F.top.rangeRestrict u)) ∈
      N.map F.top.rangeRestrict ↔ _
  rw [e.apply_symm_apply]
  constructor
  · rintro ⟨n, hn, hnu⟩
    have hk : n⁻¹ * u ∈ F.top.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hnu, inv_mul]
    have hn' : n ∈ F.top.ker ⊔ N := Subgroup.mem_sup_right hn
    have hk' : n⁻¹ * u ∈ F.top.ker ⊔ N :=
      Subgroup.mem_sup_left hk
    have hmul := (F.top.ker ⊔ N).mul_mem hn' hk'
    simpa using hmul
  · intro hu
    obtain ⟨k, hk, n, hn, hkn⟩ :=
      Subgroup.mem_sup_of_normal_right.mp hu
    refine ⟨n, hn, ?_⟩
    rw [← hkn, map_mul, MonoidHom.mem_ker.mp hk, one_mul]

theorem literalTopQuotientMap_ker_eq_zeroCutBase_ker
    (N : Subgroup U) [N.Normal] :
    (F.literalTopQuotientMap e N).ker = (F.zeroCutBase N).ker := by
  ext q
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective N q
  simp only [MonoidHom.mem_ker, F.literalTopQuotientMap_apply e N,
    F.zeroCutBase_apply, QuotientGroup.eq_one_iff]
  exact F.literalTop_mem_normal_iff e N u

/-- The intrinsic zero-cut top quotient is canonically the corresponding
quotient of the chosen literal top. -/
noncomputable def zeroCutBaseEquivLiteralTop
    (N : Subgroup U) [N.Normal] :
    (U ⟸ (F.top.ker ⊔ N)) ≃* (G ⟸ F.literalTopNormal e N) :=
  surjectiveTargetEquivOfKernelEq
    (F.zeroCutBase N) (F.literalTopQuotientMap e N)
    (F.zeroCutBase_surjective N) (F.literalTopQuotientMap_surjective e N)
    (F.literalTopQuotientMap_ker_eq_zeroCutBase_ker e N).symm

end BinaryPairFrame
end SymmetricSubgroupAsymptotics

end
