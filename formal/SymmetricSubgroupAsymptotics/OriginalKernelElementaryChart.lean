import SymmetricSubgroupAsymptotics.LinearSemidirectUniformNormalGenerators

/-! Convert an exact original kernel-module chart to elementary conjugation
coordinates. The original action agrees after inflation, so uniform module
bounds give normal generators for the actual correlated normal subkernels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
variable {p : ℕ} [Fact p.Prime] {G B : Type} [Group G] [Group B]
  (pi : G →* B) (A : Rep (ZMod p) B) [FiniteDimensional (ZMod p) A]
  (E : OriginalKernelModuleChart pi A)

def elementaryChart : ElementaryMinimalNormalChart pi.ker where
  p := p
  p_prime := Fact.out
  V := A
  equiv := E.equiv.symm

theorem elementaryChart_representation_comp :
    (E.elementaryChart pi A).quotientRepresentation.ρ.comp (QuotientGroup.mk' pi.ker)=
      A.ρ.comp pi := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro a
  let k : pi.ker := E.equiv (Multiplicative.ofAdd a)
  have hev : ((E.elementaryChart pi A).equiv k).toAdd=a := by
    change (E.equiv.symm (E.equiv (Multiplicative.ofAdd a))).toAdd=a
    simp only [E.equiv.symm_apply_apply,toAdd_ofAdd]
  have h := (E.elementaryChart pi A).quotientRepresentation_apply g k
  rw [hev] at h
  have hk : MulAut.conjNormal g k=E.equiv (Multiplicative.ofAdd (A.ρ (pi g) a)) := by
    apply Subtype.ext
    exact (E.conjugate g a).symm
  rw [hk] at h
  change (E.elementaryChart pi A).quotientRepresentation.ρ
      (QuotientGroup.mk' pi.ker g) a=
    (E.equiv.symm (E.equiv (Multiplicative.ofAdd (A.ρ (pi g) a)))).toAdd at h
  rw [E.equiv.symm_apply_apply] at h
  simpa only [toAdd_ofAdd] using h

theorem elementaryChart_uniform (hpi : Function.Surjective pi) (r : ℕ)
    (hu : UniformSubrepresentationGeneratorBound A.ρ r) :
    UniformSubrepresentationGeneratorBound (E.elementaryChart pi A).quotientRepresentation.ρ r := by
  apply UniformSubrepresentationGeneratorBound.of_comp _ (QuotientGroup.mk' pi.ker)
  rw [E.elementaryChart_representation_comp]
  exact UniformSubrepresentationGeneratorBound.comp_of_surjective A.ρ pi hpi hu

include E in
theorem kernel_normalGen_le [Finite G] (hpi : Function.Surjective pi) (r : ℕ)
    (hu : UniformSubrepresentationGeneratorBound A.ρ r)
    (M : Subgroup G) [M.Normal] (hM : M ≤ pi.ker) : MarkedC4.normalGen M ≤ r :=
  ElementaryUniformNormalGenerators.kernel_normalGen_le pi.ker (E.elementaryChart pi A)
    r (E.elementaryChart_uniform pi A hpi r hu) M hM

end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
