import SymmetricSubgroupAsymptotics.SixPairFullKernelCenterConjugation
import SymmetricSubgroupAsymptotics.OriginalKernelSectionUniform
import SymmetricSubgroupAsymptotics.OriginalKernelElementaryChart
import SymmetricSubgroupAsymptotics.PermutationPolynomialOrbitGenerators
import SymmetricSubgroupAsymptotics.ThreePointTransitiveCubicMembership

/-! The original center is the actual three-coordinate permutation module
for U/Z. The polynomial orbit-cover theorem bounds every invariant
subspace, so later original quotient sections retain the uniform one
bound; cyclic normal generation alone is not used hereditarily. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairFullKernelCenterModule
open SixPairFullKernelCenter

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I)
  (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))

abbrev Z := centerImage F E
abbrev B := U ⧸ Z F E
abbrev pi : U →* B F E := QuotientGroup.mk' (Z F E)

def factorTop : B F E →* Equiv.Perm (Fin 3) :=
  QuotientGroup.lift (Z F E) (SixPairNestedTopFrames.nestedFrame F E).top
    (centerImage_le_kernel F E)

instance pointAction : MulAction (B F E) (Fin 3) where
  smul b j := factorTop F E b j
  one_smul j := by change factorTop F E 1 j=j; rw [map_one]; rfl
  mul_smul a b j := by
    change factorTop F E (a*b) j=factorTop F E a (factorTop F E b j)
    rw [map_mul]
    rfl

abbrev moduleRep : Rep (ZMod 2) (B F E) :=
  Rep.of (permutationFunctionRepresentation (ZMod 2) (B F E) (Fin 3))

def chart (hfull : SixPairIndependentKernelNormalCommutators.Independent F E) :
    OriginalKernelModuleChart (pi F E) (moduleRep F E) where
  equiv := (SixPairFullKernelCenterBits.equiv F E hfull).symm.trans
    (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' (Z F E)).symm)
  conjugate := by
    intro g a
    let e := SixPairFullKernelCenterBits.equiv F E hfull
    let z : Z F E := e.symm (Multiplicative.ofAdd a)
    have hz : SixPairFullKernelCenterBits.bits F E z=a :=
      congrArg Multiplicative.toAdd (e.apply_symm_apply (Multiplicative.ofAdd a))
    have hh : Multiplicative.ofAdd ((moduleRep F E).ρ (pi F E g) a)=
        e (MulAut.conjNormal g z) := by
      apply Multiplicative.toAdd.injective
      funext j
      change a (factorTop F E ((pi F E g)⁻¹) j)=
        SixPairFullKernelCenterBits.bits F E (MulAut.conjNormal g z) j
      rw [map_inv]
      change a (((SixPairNestedTopFrames.nestedFrame F E).top g)⁻¹ j)=
        SixPairFullKernelCenterBits.bits F E (MulAut.conjNormal g z) j
      rw [SixPairFullKernelCenterBits.bits_conjugate F E hfull,hz]
    have he : e.symm (Multiplicative.ofAdd ((moduleRep F E).ρ (pi F E g) a))=
        MulAut.conjNormal g z := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact hh
    change (e.symm (Multiplicative.ofAdd ((moduleRep F E).ρ (pi F E g) a)) : U)=
      g*(z : U)*g⁻¹
    exact congrArg Subtype.val he

private theorem rotation_cover : ∀ i : Fin 3,∃ m : Fin 3,
    (OddMarkerTernaryChart.rotation^m.val) 0=i := by decide +kernel

/-- Uniform on all original invariant subspaces, not just the whole center. -/
theorem uniform
    (hrotation : OddMarkerTernaryChart.rotation∈
      (SixPairNestedTopFrames.nestedFrame F E).top.range) :
    UniformSubrepresentationGeneratorBound (moduleRep F E).ρ 1 := by
  obtain ⟨g,hg⟩ := hrotation
  apply permutationFunctionRepresentation_uniform_of_polynomial_orbitCover
    (pi F E g) (fun _ : Fin 1 => (0 : Fin 3))
  intro i
  obtain ⟨m,hm⟩ := rotation_cover i
  refine ⟨0,m.val,?_⟩
  change factorTop F E ((pi F E g)^m.val) 0=i
  rw [map_pow]
  change (((SixPairNestedTopFrames.nestedFrame F E).top g)^m.val) 0=i
  rw [hg]
  exact hm

end SymmetricSubgroupAsymptotics.SixPairFullKernelCenterModule
