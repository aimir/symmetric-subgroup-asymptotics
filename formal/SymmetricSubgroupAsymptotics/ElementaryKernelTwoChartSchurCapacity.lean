import SymmetricSubgroupAsymptotics.ElementaryKernelIntersectionFiltration
import SymmetricSubgroupAsymptotics.SchurMultiplicityInjectiveTarget
import SymmetricSubgroupAsymptotics.BinaryDegreeTwoKernelSchurCapacity
import SymmetricSubgroupAsymptotics.RepresentationCoordinateHeads

/-!
# Four generators from two actual elementary-kernel charts

An elementary normal section of dimension at most twelve is filtered by
the original pair kernel. The literal image has dimension at most four
when its target order divides forty-eight. The intersection embeds in the
actual pair module, so its scalar degree-two types inherit multiplicity
two there. The central fixed rank and larger Schur degrees share four
generator positions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace OriginalKernelModuleChart

theorem schurCapacity_le_four_of_two_charts
    {Q B D : Type} [Group Q] [Group B] [Finite B] [Group D]
    {eta : Q →* D} {A : Rep (ZMod 2) D} [Finite A]
    (E : OriginalKernelModuleChart eta A)
    (pi : Q →* B) {K : Rep (ZMod 2) B} [Finite K]
    (F : OriginalKernelModuleChart pi K)
    (hdim : Module.finrank (ZMod 2) A ≤ 12)
    (hfixed : Module.finrank (ZMod 2) (inflatedRepresentation eta A.ρ).invariants ≤ 4)
    (hcard : Nat.card B ∣ 48)
    (hpair : ∀ {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
      [FiniteDimensional (ZMod 2) W] (sigma : Representation (ZMod 2) Q W),
      [IsSimpleModule (ZMod 2)[Q] sigma.asModule] →
      Module.finrank (ZMod 2) W = 2 →
      Module.finrank (ZMod 2) (Module.End (ZMod 2)[Q] sigma.asModule) = 2 →
      schurSocleMultiplicity (k := ZMod 2) (R := (ZMod 2)[Q])
        (A := (inflatedRepresentation pi K.ρ).asModule) (X := sigma.asModule) ≤ 2) :
    representationSchurCapacity (inflatedRepresentation eta A.ρ) ≤ 4 := by
  let rho := inflatedRepresentation eta A.ρ
  let J := E.kernelIntersection pi
  let tau := E.kernelImageRepresentation pi
  let q := E.kernelImageProjection pi
  apply representationSchurCapacity_le_four_of_degreeTwo_kernel rho tau q
    (E.kernelImageProjection_surjective pi) hdim hfixed
    (E.kernelImage_finrank_le pi (d := 4) (by simpa using hcard))
  intro S _hS hnonfixed hdegree
  letI : FiniteDimensional (ZMod 2) S := FiniteDimensional.of_injective
    (S.subtype.restrictScalars (ZMod 2)) S.subtype_injective
  let sigmaS := (Subrepresentation.ofSubmodule' S).toRepresentation
  let eS := submoduleRepresentationModuleEquiv rho S
  letI : IsSimpleModule (ZMod 2)[Q] sigmaS.asModule := IsSimpleModule.congr eS.symm
  have hdimS : Module.finrank (ZMod 2) (Subrepresentation.ofSubmodule' S).toSubmodule = 2 := by
    calc
      _ = Module.finrank (ZMod 2) sigmaS.asModule := sigmaS.asModuleEquiv.finrank_eq.symm
      _ = Module.finrank (ZMod 2) S := (eS.restrictScalars (ZMod 2)).finrank_eq.symm
      _ = 2 := (schurSimpleProductDegree_eq_two_profile rho S hnonfixed hdegree).1
  have hEndS : Module.finrank (ZMod 2)
      (Module.End (ZMod 2)[Q] sigmaS.asModule) = 2 :=
    (moduleEnd_finrank_eq_of_linearEquiv (k := ZMod 2) eS).symm.trans
      (schurSimpleProductDegree_eq_two_end_finrank rho S hnonfixed hdegree)
  have hp := hpair sigmaS hdimS hEndS
  rw [← schurSocleMultiplicity_eq_of_source_linearEquiv
    (k := ZMod 2) (R := (ZMod 2)[Q])
    (A := (inflatedRepresentation pi K.ρ).asModule) eS] at hp
  let eJ := submoduleRepresentationModuleEquiv rho J.asSubmodule
  let f : J.asSubmodule →ₗ[(ZMod 2)[Q]] (inflatedRepresentation pi K.ρ).asModule :=
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _
      (E.kernelIntersectionIntertwiner pi F)).comp eJ.toLinearMap
  have hf : Function.Injective f :=
    (E.kernelIntersectionIntertwiner_injective pi F).comp eJ.injective
  letI : FiniteDimensional (ZMod 2) J.asSubmodule := FiniteDimensional.of_injective
    (J.asSubmodule.subtype.restrictScalars (ZMod 2)) J.asSubmodule.subtype_injective
  have hle := schurSocleMultiplicity_le_of_injective_target
    (k := ZMod 2) (R := (ZMod 2)[Q]) (X := S) f hf
  rw [E.kernelImageProjection_ker pi]
  exact hle.trans hp

end OriginalKernelModuleChart
end SymmetricSubgroupAsymptotics

end
