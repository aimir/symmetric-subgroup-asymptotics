import SymmetricSubgroupAsymptotics.BinaryCubicKernelClassProjectors
import SymmetricSubgroupAsymptotics.BinaryPlaneKleinKernelGeometry
import SymmetricSubgroupAsymptotics.BinaryPlaneRankOneKleinUniform

/-! Universal translation capacity two for actual NONBINARY linear images
with full regular V4 block top. The constant kernel partition is the
rank-one cubic case; every other actual partition uses kernel averages.
No common cubic element is assumed in the higher-rank branch. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPlaneKleinUniform
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathActualOddKernel
abbrev R := BinaryRegularKleinWreath.R
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq

variable (C : Subgroup (W (R := R) (I := R)))
abbrev representation := BinaryPlaneCyclicWreathUniform.representation C

theorem uniform (hC : ¬ IsPGroup 2 C)
    (honto : Function.Surjective
      ((PermutationalWreathProduct.rightHom : W (R := R) (I := R) →* R).comp C.subtype)) :
    UniformSubrepresentationGeneratorBound (representation C) 2 := by
  have hR : IsPGroup 2 R := by
    intro r
    exact ⟨1,(by decide +kernel : ∀ r : R, r^2=1) r⟩
  have hO : oddKernel C≠⊥ := oddKernel_ne_bot C hR hC
  by_cases hconstant : ∀ i : R, BinaryPlaneKleinKernelGeometry.localKernel C i=
      BinaryPlaneKleinKernelGeometry.localKernel C 1
  · exact BinaryPlaneRankOneKleinUniform.uniform C
      (BinaryPlaneKleinKernelGeometry.rankOneEquiv C hO hconstant) honto
  · obtain ⟨color,hcolor⟩ := BinaryPlaneKleinKernelGeometry.exists_colors C honto hconstant
    have htrans : ∀ i j : R, ∃ h : C, (h : W (R := R) (I := R)).right • i=j := by
      intro i j
      obtain ⟨h,hh⟩ := honto (j*i⁻¹)
      refine ⟨h,?_⟩
      change (h : W (R := R) (I := R)).right*i=j
      change (h : W (R := R) (I := R)).right=j*i⁻¹ at hh
      rw [hh]
      group
    let rho : Representation (ZMod 2) (oddKernel C) (R → Plane) :=
      (representation C).comp (oddKernel C).subtype
    let L : R → oddKernel C →* Linear := localLinear C
    have happly : ∀ g v i, rho g v i=L i g (v i) := by
      intro g v i
      change localLinear C i g (v (((g : C) : W (R := R) (I := R)).right⁻¹ • i))=L i g (v i)
      rw [top_one C g,inv_one,one_smul]
    have hcards : ∀ i j,
        Nat.card (BinaryCubicKernelClassProjectors.localKernel L i)=
          Nat.card (BinaryCubicKernelClassProjectors.localKernel L j) :=
      BinaryPlaneKleinKernelGeometry.localKernel_card_eq C honto
    have hlocal : ∀ i, ∃ g : oddKernel C, L i g≠1 :=
      all_local_nontrivial C hO htrans
    have hkernel := BinaryCubicKernelClassProjectors.uniform_two rho L happly
      (isPGroup_three C) (local_cubic C) hlocal hcards color hcolor
    exact UniformSubrepresentationGeneratorBound.of_comp (representation C)
      (oddKernel C).subtype hkernel

/-- Original normal quotients can use their literal retained translation
subspace and projection, without a proxy normal denominator. -/
theorem section_uniform (hC : ¬ IsPGroup 2 C)
    (honto : Function.Surjective
      ((PermutationalWreathProduct.rightHom : W (R := R) (I := R) →* R).comp C.subtype))
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (S : Subrepresentation (representation C)) (sigma : Representation (ZMod 2) C V)
    (q : Representation.IntertwiningMap S.toRepresentation sigma)
    (hq : Function.Surjective q) : UniformSubrepresentationGeneratorBound sigma 2 := by
  let F : Representation.IntertwiningMap S.toRepresentation (representation C) :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' _ := rfl }
  exact ((uniform C hC honto).of_injective F Subtype.val_injective).of_surjective q hq

end SymmetricSubgroupAsymptotics.BinaryPlaneKleinUniform
