import SymmetricSubgroupAsymptotics.BinaryPairZeroCutExtension
import SymmetricSubgroupAsymptotics.BinaryPairLargeSectionCharacter
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

/-- The kernel retained while passing to any literal model of the pair top
is the actual elementary binary zero-cut kernel. -/
theorem literalTopQuotientMap_kernel_isPGroup
    (N : Subgroup U) [N.Normal] :
    IsPGroup 2 (F.literalTopQuotientMap e N).ker := by
  rw [F.literalTopQuotientMap_ker_eq_zeroCutBase_ker e N]
  have hmodule : IsPGroup 2 (Multiplicative (F.zeroCutModule N)) :=
    primeModule_isPGroup 2 (F.zeroCutModule N)
  exact hmodule.of_equiv (F.zeroCutKernelEquiv N)

/-- The intrinsic zero-cut top quotient is canonically the corresponding
quotient of the chosen literal top. -/
noncomputable def zeroCutBaseEquivLiteralTop
    (N : Subgroup U) [N.Normal] :
    (U ⟸ (F.top.ker ⊔ N)) ≃* (G ⟸ F.literalTopNormal e N) :=
  surjectiveTargetEquivOfKernelEq
    (F.zeroCutBase N) (F.literalTopQuotientMap e N)
    (F.zeroCutBase_surjective N) (F.literalTopQuotientMap_surjective e N)
    (F.literalTopQuotientMap_ker_eq_zeroCutBase_ker e N).symm

/-- The target equivalence sends the actual top quotient to the literal top
quotient on every lifted top element. -/
@[simp] theorem zeroCutBaseEquivLiteralTop_sectionTopQuotient
    (N : Subgroup U) [N.Normal] (g : G) :
    F.zeroCutBaseEquivLiteralTop e N
        (F.sectionTopQuotient N (e g)) =
      QuotientGroup.mk' (F.literalTopNormal e N) g := by
  obtain ⟨u, hu⟩ := F.top.rangeRestrict_surjective (e g)
  have hcomp := congrArg (fun h : (U ⧸ N) →*
      (G ⧸ F.literalTopNormal e N) =>
      h (QuotientGroup.mk' N u))
    (surjectiveTargetEquivOfKernelEq_comp
      (F.zeroCutBase N) (F.literalTopQuotientMap e N)
      (F.zeroCutBase_surjective N)
      (F.literalTopQuotientMap_surjective e N)
      (F.literalTopQuotientMap_ker_eq_zeroCutBase_ker e N).symm)
  change F.zeroCutBaseEquivLiteralTop e N
      (QuotientGroup.mk' (F.top.ker ⊔ N) u) =
    QuotientGroup.mk' (F.literalTopNormal e N)
      (e.symm (F.top.rangeRestrict u)) at hcomp
  rw [← F.sectionTopQuotient_apply N u, hu,
    e.symm_apply_apply] at hcomp
  exact hcomp

/-- The actual zero-cut module, with its acting quotient transported to the
chosen literal top quotient. -/
def literalZeroCutModule
    (N : Subgroup U) [N.Normal] :
    Rep (ZMod 2) (G ⟸ F.literalTopNormal e N) :=
  Rep.of ((F.zeroCutModule N).ρ.comp
    (F.zeroCutBaseEquivLiteralTop e N).symm.toMonoidHom)

/-- Module chart on the literal-top quotient map.  This is the zero-cut
chart itself with only the acting quotient relabelled. -/
noncomputable def literalZeroCutModuleChart
    (N : Subgroup U) [N.Normal] :
    OriginalKernelModuleChart (F.literalTopQuotientMap e N)
      (F.literalZeroCutModule e N) where
  equiv := (F.zeroCutKernelEquiv N).trans
    (MulEquiv.subgroupCongr
      (F.literalTopQuotientMap_ker_eq_zeroCutBase_ker e N).symm)
  conjugate q a := by
    have hcomp := congrArg (fun h : (U ⟸ N) →*
        (G ⟸ F.literalTopNormal e N) => h q)
      (surjectiveTargetEquivOfKernelEq_comp
        (F.zeroCutBase N) (F.literalTopQuotientMap e N)
        (F.zeroCutBase_surjective N)
        (F.literalTopQuotientMap_surjective e N)
        (F.literalTopQuotientMap_ker_eq_zeroCutBase_ker e N).symm)
    have hbase :
        (F.zeroCutBaseEquivLiteralTop e N).symm
            (F.literalTopQuotientMap e N q) = F.zeroCutBase N q := by
      rw [← hcomp]
      exact (F.zeroCutBaseEquivLiteralTop e N).symm_apply_apply _
    change
      ((F.zeroCutKernelEquiv N)
          (Multiplicative.ofAdd
            ((F.zeroCutModule N).ρ
              ((F.zeroCutBaseEquivLiteralTop e N).symm
                (F.literalTopQuotientMap e N q)) a)) : U ⟸ N) =
        q * ((F.zeroCutKernelEquiv N) (Multiplicative.ofAdd a) : U ⟸ N) * q⁻¹
    rw [hbase]
    exact (F.zeroCutModuleChart N).conjugate q a

/-- The undoubled section module with its acting quotient transported to
the chosen literal top quotient. -/
def literalSectionModule
    (N : Subgroup U) [N.Normal] :
    Rep (ZMod 2) (G ⟸ F.literalTopNormal e N) :=
  Rep.of ((F.sectionRepresentation N).comp
    (F.zeroCutBaseEquivLiteralTop e N).symm.toMonoidHom)

/-- Inflating the literal section to the literal top recovers the actual
section-top representation after transport along the chosen top
equivalence. -/
def sectionTopEquivLiteralSectionInflation
    (N : Subgroup U) [N.Normal] :
    ((F.sectionTopRepresentation N).comp e.toMonoidHom).Equiv
      ((F.literalSectionModule e N).ρ.comp
        (QuotientGroup.mk' (F.literalTopNormal e N))) :=
  Representation.Equiv.mk
    (LinearEquiv.refl (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N)) (by
      intro g
      apply LinearMap.ext
      intro v
      change F.sectionRepresentation N (F.sectionTopQuotient N (e g)) v =
        F.sectionRepresentation N
          ((F.zeroCutBaseEquivLiteralTop e N).symm
            (QuotientGroup.mk' (F.literalTopNormal e N) g)) v
      rw [← F.zeroCutBaseEquivLiteralTop_sectionTopQuotient e N g,
        (F.zeroCutBaseEquivLiteralTop e N).symm_apply_apply])

/-- Module chart for the same literal quotient using the direct section
`kernelSpace / normalSpace`, which is more convenient for lifting finite
coordinate subspaces. -/
noncomputable def literalSectionModuleChart
    (N : Subgroup U) [N.Normal] :
    OriginalKernelModuleChart (F.literalTopQuotientMap e N)
      (F.literalSectionModule e N) where
  equiv := (F.sectionKernelEquiv N).trans
    (MulEquiv.subgroupCongr
      (F.literalTopQuotientMap_ker_eq_zeroCutBase_ker e N).symm)
  conjugate q a := by
    have hcomp := congrArg (fun h : (U ⟸ N) →*
        (G ⟸ F.literalTopNormal e N) => h q)
      (surjectiveTargetEquivOfKernelEq_comp
        (F.zeroCutBase N) (F.literalTopQuotientMap e N)
        (F.zeroCutBase_surjective N)
        (F.literalTopQuotientMap_surjective e N)
        (F.literalTopQuotientMap_ker_eq_zeroCutBase_ker e N).symm)
    have hbase :
        (F.zeroCutBaseEquivLiteralTop e N).symm
            (F.literalTopQuotientMap e N q) = F.zeroCutBase N q := by
      rw [← hcomp]
      exact (F.zeroCutBaseEquivLiteralTop e N).symm_apply_apply _
    change
      ((F.sectionKernelEquiv N)
          (Multiplicative.ofAdd
            (F.sectionRepresentation N
              ((F.zeroCutBaseEquivLiteralTop e N).symm
                (F.literalTopQuotientMap e N q)) a)) : U ⟸ N) =
        q * ((F.sectionKernelEquiv N) (Multiplicative.ofAdd a) : U ⟸ N) * q⁻¹
    rw [hbase]
    exact (F.sectionModuleChart N).conjugate q a

/-- On a literal kernel element, the transported section chart is still the
original quotient coset. -/
@[simp] theorem literalSectionModuleChart_equiv_mk
    (N : Subgroup U) [N.Normal] (k : F.top.ker) :
    (((F.literalSectionModuleChart e N).equiv
      (Multiplicative.ofAdd
        ((F.normalSpace N).mkQ (F.kernelSpaceHom k).toAdd)) :
          (F.literalTopQuotientMap e N).ker) : U ⧸ N) =
      QuotientGroup.mk' N (k : U) := by
  change (((MulEquiv.subgroupCongr
      (F.literalTopQuotientMap_ker_eq_zeroCutBase_ker e N).symm)
        (F.sectionKernelEquiv N
          (F.sectionMap N k)) :
            (F.literalTopQuotientMap e N).ker) : U ⧸ N) = _
  rw [F.sectionKernelEquiv_apply N k]
  rfl

end BinaryPairFrame
end SymmetricSubgroupAsymptotics

end
