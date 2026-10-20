import SymmetricSubgroupAsymptotics.SixteenPointSemanticDihedralActualSource
import SymmetricSubgroupAsymptotics.BinaryPlaneWreathLinearModelEquiv
import SymmetricSubgroupAsymptotics.LinearSemidirectActualImageKernelChart
import SymmetricSubgroupAsymptotics.OriginalKernelChartEquivTransport

/-! Universal actual-subgroup recognition constructor for the D8 quartet
family. Kernel charts, correlated translation inclusions, interval bounds,
and original-weight numerics are constructed rather than assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.SixteenPointSemanticDihedralSubgroupSource
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathLinearModelEquiv LinearSemidirectSubgroupKernelChart
open Non2UnipotentPrefixFiniteMenu
open DihedralEightRegularKleinBlockModel (R Q)
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq

def source (K : Subgroup (PointwiseModel (R := Q) (I := R)))
    (hK : ¬ IsPGroup 2 K)
    (hblocks : Function.Surjective
      ((PermutationalWreathProduct.rightHom : W (R := Q) (I := R) →* Q).comp
        ((SemidirectProduct.rightHom : PointwiseModel (R := Q) (I := R) →*
          W (R := Q) (I := R)).comp K.subtype)))
    (i : PreE7NonPairActionClass 16) (originalEquiv : K ≃* preE7NonPairAction 16 i)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (family : PreE7NoPairNoC3EarlierOwnerFamily) :
    PreE7RankTailSourceOrYonedaTopData 16 i := by
  let a := BinaryPlaneWreathLinearModelEquiv.equiv (R := Q) (I := R)
  let J := K.map a.toMonoidHom
  let eK : K ≃* J := a.subgroupMap K
  let e := originalEquiv.symm.trans eK
  let rho := BinaryPlaneWreathLinearModelEquiv.linear (R := Q) (I := R)
  let C := Image rho J
  let pi₀ := LinearSemidirectActualImageKernelChart.top rho J
  let A := LinearSemidirectActualImageKernelChart.kernelModule rho J
  let E₀ := LinearSemidirectActualImageKernelChart.originalKernelChart rho J
  let pi := pi₀.comp e.toMonoidHom
  let E := E₀.ofSourceEquiv pi₀ A e
  have hpi : Function.Surjective pi :=
    (projection rho J).rangeRestrict_surjective.comp e.surjective
  let j : Representation.IntertwiningMap A.ρ (BinaryPlaneCyclicWreathUniform.representation C) :=
    LinearSemidirectActualImageKernelChart.inclusion rho J
  have hj : Function.Injective j := LinearSemidirectActualImageKernelChart.inclusion_injective rho J
  have hCblocks : Function.Surjective
      ((PermutationalWreathProduct.rightHom : W (R := Q) (I := R) →* Q).comp C.subtype) := by
    intro r
    obtain ⟨g,hg⟩ := hblocks r
    exact ⟨(projection rho J).rangeRestrict (eK g),hg⟩
  have hU : ¬ IsPGroup 2 (preE7NonPairAction 16 i) := fun hp =>
    hK (hp.of_injective originalEquiv.toMonoidHom originalEquiv.injective)
  exact SixteenPointSemanticDihedralActualSource.source i C pi hpi A E j hj hCblocks hU
    hMN hZmud lit family

end SymmetricSubgroupAsymptotics.SixteenPointSemanticDihedralSubgroupSource
