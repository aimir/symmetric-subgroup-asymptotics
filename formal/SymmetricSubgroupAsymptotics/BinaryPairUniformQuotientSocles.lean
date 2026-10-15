import SymmetricSubgroupAsymptotics.BinaryPairFrameEquivariance
import SymmetricSubgroupAsymptotics.LinearSemidirectUniformNormalGenerators
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators
import SymmetricSubgroupAsymptotics.NormalGeneratorQuotientSocles

/-! Uniform quotient-socle bounds from an original physical pair frame.
The elementary chart is the exact correlated flip space, and the quotient
is the actual pair-action range. Offsets cancel in conjugation, so no
splitting of the original pair extension is required. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} [Finite X] [Fintype I]
  {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)

def elementaryKernelChart : ElementaryMinimalNormalChart F.top.ker where
  p := 2
  p_prime := Nat.prime_two
  V := F.kernelSpace
  equiv := F.kernelChart

def kernelRepresentationInclusion :
    Representation.IntertwiningMap (A := ZMod 2) (V := F.kernelSpace) (W := I → ZMod 2)
    (F.elementaryKernelChart.quotientRepresentation.ρ.comp
      (QuotientGroup.mk' F.top.ker))
        ((permutationFunctionRepresentation (ZMod 2) F.top.range I).comp F.top.rangeRestrict) where
  toLinearMap := F.kernelSpace.subtype
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    let e : F.top.ker := F.kernelChart.symm (Multiplicative.ofAdd v)
    have hev : (F.elementaryKernelChart.equiv e).toAdd = v :=
      congrArg Multiplicative.toAdd (F.kernelChart.apply_symm_apply _)
    have hbits : F.bits e = (v : I → ZMod 2) :=
      congrArg (fun w : F.kernelSpace => (w : I → ZMod 2)) hev
    have h := F.elementaryKernelChart.quotientRepresentation_apply g e
    rw [hev] at h
    have hc := congrArg (fun w : F.kernelSpace => (w : I → ZMod 2)) h
    change Subtype.val (p := fun v : I → ZMod 2 => v ∈ F.kernelSpace)
      (F.elementaryKernelChart.quotientRepresentation.ρ
        (QuotientGroup.mk' F.top.ker g) v) =
        F.bits (MulAut.conjNormal g e) at hc
    change Subtype.val (p := fun v : I → ZMod 2 => v ∈ F.kernelSpace)
      (F.elementaryKernelChart.quotientRepresentation.ρ
        (QuotientGroup.mk' F.top.ker g) v) =
        fun i => v.val ((F.top g)⁻¹ i)
    rw [hc]
    funext i
    rw [F.bits_conjNormal,hbits]

omit [Finite X] in
theorem elementaryKernelChart_uniform (t : ℕ)
    (huniform : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range I) t) :
    UniformSubrepresentationGeneratorBound F.elementaryKernelChart.quotientRepresentation.ρ t := by
  apply UniformSubrepresentationGeneratorBound.of_comp
    F.elementaryKernelChart.quotientRepresentation.ρ (QuotientGroup.mk' F.top.ker)
  have h := UniformSubrepresentationGeneratorBound.comp_of_surjective
    (permutationFunctionRepresentation (ZMod 2) F.top.range I) F.top.rangeRestrict
    F.top.rangeRestrict_surjective huniform
  exact h.of_injective F.kernelRepresentationInclusion (fun _ _ he => Subtype.ext he)

theorem normalGen_le_of_uniform_pair_action (t a : ℕ)
    (huniform : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range I) t)
    (htop : ∀ L : Subgroup F.top.range, L.Normal → MarkedC4.normalGen L ≤ a)
    (N : Subgroup U) [N.Normal] : MarkedC4.normalGen N ≤ t+a := by
  apply ElementaryUniformNormalGenerators.normalGen_le F.top.ker F.elementaryKernelChart
    t a (F.elementaryKernelChart_uniform t huniform) ?_ N
  intro L hL
  letI := hL
  let e : U ⧸ F.top.ker ≃* F.top.range := QuotientGroup.quotientKerEquivRange F.top
  exact CoprimeKernelQuotientSocles.normalGen_image_bound
    e.symm.toMonoidHom e.symm.surjective a htop L

theorem quotientSocle_of_uniform_pair_action (t a : ℕ)
    (huniform : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range I) t)
    (htop : ∀ L : Subgroup F.top.range, L.Normal → MarkedC4.normalGen L ≤ a)
    (N : Subgroup U) [N.Normal] : SocleNormalGeneratorBound (U ⧸ N) (t+a) := by
  apply quotientSocleNormalGeneratorBound_of_normal_generating_tuples ?_ N
  intro L hL
  letI := hL
  exact exists_normal_generating_tuple_of_normalGen_le L
    (F.normalGen_le_of_uniform_pair_action t a huniform htop L)

end SymmetricSubgroupAsymptotics.BinaryPairFrame

end
