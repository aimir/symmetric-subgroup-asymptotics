import SymmetricSubgroupAsymptotics.SixteenPointSemanticAlternatingRankOneActualSource
import SymmetricSubgroupAsymptotics.BinaryPlaneWreathLinearModelEquiv
import SymmetricSubgroupAsymptotics.LinearSemidirectActualImageKernelChart
import SymmetricSubgroupAsymptotics.OriginalKernelChartEquivTransport

/-! Universal actual-subgroup recognition constructor for the rank-one A4/S4 quartet
family. Kernel charts, correlated translation inclusions, interval bounds,
and original-weight numerics are constructed rather than assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.SixteenPointSemanticAlternatingRankOneSubgroupSource
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathLinearModelEquiv LinearSemidirectSubgroupKernelChart
open Non2UnipotentPrefixFiniteMenu
open BinaryPlaneAlternatingKernelPartition (Frame Cubic)
open BinaryPlaneWreathActualOddKernel
abbrev R := Fin 4
abbrev Q := Equiv.Perm (Fin 4)

def linearImage (K : Subgroup (PointwiseModel (R := Q) (I := R))) : Subgroup Frame :=
  Image (BinaryPlaneWreathLinearModelEquiv.linear (R := Q) (I := R))
    (K.map (BinaryPlaneWreathLinearModelEquiv.equiv (R := Q) (I := R)).toMonoidHom)

def source (K : Subgroup (PointwiseModel (R := Q) (I := R)))
    (hK : ¬ IsPGroup 2 K)
    (cubicChart : oddKernel (linearImage K) ≃* Cubic)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : linearImage K, (h : Frame).right=p.val)
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
  let C := linearImage K
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
  have hU : ¬ IsPGroup 2 (preE7NonPairAction 16 i) := fun hp =>
    hK (hp.of_injective originalEquiv.toMonoidHom originalEquiv.injective)
  exact SixteenPointSemanticAlternatingRankOneActualSource.source i C cubicChart heven pi hpi A E j hj hU
    hMN hZmud lit family

end SymmetricSubgroupAsymptotics.SixteenPointSemanticAlternatingRankOneSubgroupSource
