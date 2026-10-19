import SymmetricSubgroupAsymptotics.SixPairProperCentralQuotientSocle
import SymmetricSubgroupAsymptotics.SixPairFullKernelCenterModule
import SymmetricSubgroupAsymptotics.NormalGeneratorQuotientSocles

/-! Every proper original central quotient has socle-normal-generator
bound ONE. The proof uses the actual invariant quotient section of the
original three-bit center module, not subgroup inheritance of generation. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairProperCentralQuotientSocleOne
open SixPairFullKernelCenter SixPairFullKernelCenterModule OriginalKernelModuleChart

variable {X I : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I)
  (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))

/-- An actual all-original-denominator conclusion for the below-center
branch of the full-independent three-pair model. -/
theorem socle_bound [MulAction.IsPretransitive U X]
    (hfull : SixPairIndependentKernelNormalCommutators.Independent F E)
    (N : Subgroup U) [N.Normal] (hN : N≤centerImage F E)
    (hproper : ¬centerImage F E≤N) : SocleNormalGeneratorBound (U ⧸ N) 1 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A := moduleRep F E
  let D := chart F E hfull
  have hpi : Function.Surjective (pi F E) := QuotientGroup.mk'_surjective _
  have hrotation := ThreePointTransitiveCubicMembership.frame_rotation_mem
    (SixPairNestedTopFrames.nestedFrame F E)
    (fun x y => MulAction.exists_smul_eq U x y)
  have hu : UniformSubrepresentationGeneratorBound A.ρ 1 := uniform F E hrotation
  have hs := D.sectionUniform (pi F E) A N hpi hu
  letI : FiniteDimensional (ZMod 2) (D.sectionRepresentation (pi F E) A N) := by
    change FiniteDimensional (ZMod 2) (D.sectionModule (pi F E) A N)
    infer_instance
  have hi : finiteGroupSocle (U ⧸ N)≤(base (pi F E) N).ker := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ :=
      SixPairProperCentralQuotientSocle.socle_le_center_image F E hfull N hN hproper hx
    rw [MonoidHom.mem_ker,base_apply]
    apply (QuotientGroup.eq_one_iff _).mpr
    apply Subgroup.mem_sup_left
    simpa only [pi,QuotientGroup.ker_mk'] using hz
  have hn : MarkedC4.normalGen (finiteGroupSocle (U ⧸ N))≤1 :=
    (D.quotientChart (pi F E) A N).kernel_normalGen_le (base (pi F E) N)
      (D.sectionRepresentation (pi F E) A N) (base_surjective (pi F E) N) 1 hs _ hi
  exact (socleNormalGeneratorBound_iff_normalGen_le (U ⧸ N) 1).mpr hn

end SymmetricSubgroupAsymptotics.SixPairProperCentralQuotientSocleOne
