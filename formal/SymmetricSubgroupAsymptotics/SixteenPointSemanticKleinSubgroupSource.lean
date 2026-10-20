import SymmetricSubgroupAsymptotics.SixteenPointSemanticKleinActualSource
import SymmetricSubgroupAsymptotics.BinaryPlaneWreathLinearModelEquiv
import SymmetricSubgroupAsymptotics.LinearSemidirectActualImageKernelChart
import SymmetricSubgroupAsymptotics.OriginalKernelChartEquivTransport

/-! Universal actual-subgroup recognition constructor for the V4 quartet
family. Kernel charts, correlated translation inclusions, interval bounds,
and original-weight numerics are constructed rather than assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.SixteenPointSemanticKleinSubgroupSource
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathLinearModelEquiv LinearSemidirectSubgroupKernelChart
open Non2UnipotentPrefixFiniteMenu
abbrev R := BinaryRegularKleinWreath.R
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq

def source (K : Subgroup (PointwiseModel (R := R) (I := R)))
    (hK : ¬ IsPGroup 2 K)
    (hblocks : Function.Surjective
      ((PermutationalWreathProduct.rightHom : W (R := R) (I := R) →* R).comp
        ((SemidirectProduct.rightHom : PointwiseModel (R := R) (I := R) →*
          W (R := R) (I := R)).comp K.subtype)))
    (i : PreE7NonPairActionClass 16) (originalEquiv : K ≃* preE7NonPairAction 16 i)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (family : PreE7NoPairNoC3EarlierOwnerFamily) :
    PreE7RankTailSourceOrYonedaTopData 16 i := by
  let a := BinaryPlaneWreathLinearModelEquiv.equiv (R := R) (I := R)
  let J := K.map a.toMonoidHom
  let eK : K ≃* J := a.subgroupMap K
  let e := originalEquiv.symm.trans eK
  let rho := BinaryPlaneWreathLinearModelEquiv.linear (R := R) (I := R)
  let C := Image rho J
  let pi₀ := LinearSemidirectActualImageKernelChart.top rho J
  let A := LinearSemidirectActualImageKernelChart.kernelModule rho J
  let E₀ := LinearSemidirectActualImageKernelChart.originalKernelChart rho J
  let pi := pi₀.comp e.toMonoidHom
  let E := E₀.ofSourceEquiv pi₀ A e
  have hpi : Function.Surjective pi :=
    (projection rho J).rangeRestrict_surjective.comp e.surjective
  let j : Representation.IntertwiningMap A.ρ (BinaryPlaneKleinUniform.representation C) :=
    LinearSemidirectActualImageKernelChart.inclusion rho J
  have hj : Function.Injective j := LinearSemidirectActualImageKernelChart.inclusion_injective rho J
  have hCblocks : Function.Surjective
      ((PermutationalWreathProduct.rightHom : W (R := R) (I := R) →* R).comp C.subtype) := by
    intro r
    obtain ⟨g,hg⟩ := hblocks r
    exact ⟨(projection rho J).rangeRestrict (eK g),hg⟩
  have hU : ¬ IsPGroup 2 (preE7NonPairAction 16 i) := fun hp =>
    hK (hp.of_injective originalEquiv.toMonoidHom originalEquiv.injective)
  exact SixteenPointSemanticKleinActualSource.source i C pi hpi A E j hj hCblocks hU
    hMN hZmud lit family

end SymmetricSubgroupAsymptotics.SixteenPointSemanticKleinSubgroupSource
