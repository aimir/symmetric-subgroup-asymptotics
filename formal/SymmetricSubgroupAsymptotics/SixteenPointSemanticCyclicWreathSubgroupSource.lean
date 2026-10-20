import SymmetricSubgroupAsymptotics.SixteenPointSemanticCyclicActualKernelSource
import SymmetricSubgroupAsymptotics.BinaryPlaneWreathLinearModelEquiv
import SymmetricSubgroupAsymptotics.LinearSemidirectActualImageKernelChart

/-! Universal actual-subgroup constructor for cyclic binary-plane affine
wreaths. Its kernel chart and correlated kernel inclusion are constructed
from the literal subgroup; neither is an extra consumer premise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.SixteenPointSemanticCyclicWreathSubgroupSource
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathLinearModelEquiv LinearSemidirectSubgroupKernelChart
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {R I : Type} [Group R] [Finite R] [IsCyclic R] [MulAction R I]
  [Fintype I] [DecidableEq I]

/-- Complete original-weight source for EVERY nonbinary actual subgroup
with a full cyclic binary block image. No local Singer/projector condition
or assumed quotient-socle bound remains in the interface. -/
def source (K : Subgroup (PointwiseModel (R := R) (I := I)))
    (hK : ¬ IsPGroup 2 K)
    (hblocks : Function.Surjective
      ((PermutationalWreathProduct.rightHom : W (R := R) (I := I) →* R).comp
        ((SemidirectProduct.rightHom : PointwiseModel (R := R) (I := I) →*
          W (R := R) (I := I)).comp K.subtype)))
    (c : R) (i₀ : I) (hcycle : ∀ i : I, ∃ n : ℕ, c^n • i₀=i)
    (hR : IsPGroup 2 R)
    (i : PreE7NonPairActionClass 16)
    (phi : K →* preE7NonPairAction 16 i) (hphi : Function.Surjective phi)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PreE7RankTailSourceOrYonedaTopData 16 i := by
  let e := BinaryPlaneWreathLinearModelEquiv.equiv (R := R) (I := I)
  let J := K.map e.toMonoidHom
  let eK : K ≃* J := e.subgroupMap K
  let rho := BinaryPlaneWreathLinearModelEquiv.linear (R := R) (I := I)
  let C := Image rho J
  let top := LinearSemidirectActualImageKernelChart.top rho J
  let A := LinearSemidirectActualImageKernelChart.kernelModule rho J
  let E := LinearSemidirectActualImageKernelChart.originalKernelChart rho J
  have htop : Function.Surjective top := (projection rho J).rangeRestrict_surjective
  have hJ : ¬ IsPGroup 2 J := fun hp ↦
    hK (hp.of_injective eK.toMonoidHom eK.injective)
  have hCblocks : Function.Surjective
      ((PermutationalWreathProduct.rightHom : W (R := R) (I := I) →* R).comp C.subtype) := by
    intro r
    obtain ⟨g,hg⟩ := hblocks r
    refine ⟨(projection rho J).rangeRestrict (eK g),?_⟩
    exact hg
  let j : Representation.IntertwiningMap A.ρ (BinaryPlaneCyclicWreathUniform.representation C) :=
    LinearSemidirectActualImageKernelChart.inclusion rho J
  have hj : Function.Injective j :=
    LinearSemidirectActualImageKernelChart.inclusion_injective rho J
  exact SixteenPointSemanticCyclicActualKernelSource.source
    C top htop A E j hj hCblocks c i₀ hcycle hR hJ i
    (phi.comp eK.symm.toMonoidHom) (hphi.comp eK.symm.surjective) hMN hZmud

end SymmetricSubgroupAsymptotics.SixteenPointSemanticCyclicWreathSubgroupSource
