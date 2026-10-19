import SymmetricSubgroupAsymptotics.SixteenPointSemanticAlternatingZeroOddRecognition
import SymmetricSubgroupAsymptotics.SixteenPointSemanticAlternatingNonzeroOddActualSource

/-! Complete actual A4/S4 quartet recognition cover at every odd rank:
the original eight-pair geometry is retained as an explicit alternative. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixteenPointSemanticAlternatingActualRecognition
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneWreathActualOddKernel
open BinaryPlaneLineFramePairing (Affine Point)
open Non2UnipotentPrefixFiniteMenu

theorem pair_or_source (i : PreE7NonPairActionClass 16) (C : Subgroup Frame)
    (rho : preE7NonPairAction 16 i →* Affine)
    (pi : preE7NonPairAction 16 i →* C) (hpi : Function.Surjective pi)
    (hlinear : ∀ u, (rho u).right=(pi u : Frame))
    (pointChart : Point ≃ Fin 16)
    (hpoint : ∀ (u : preE7NonPairAction 16 i) p,
      pointChart (BinaryPlanePermutationWreathCoordinates.pointAction (rho u) p)=
        (u : Equiv.Perm (Fin 16)) (pointChart p))
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    (A : Rep.{0} (ZMod 2) C) (E : OriginalKernelModuleChart pi A)
    (j : Representation.IntertwiningMap A.ρ (BinaryPlaneCyclicWreathUniform.representation C))
    (hj : Function.Injective j)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (family : PreE7NoPairNoC3EarlierOwnerFamily) :
    Nonempty (BinaryPairFrame (preE7NonPairAction 16 i) (Fin 8)) ∨
      Nonempty (PreE7RankTailSourceOrYonedaTopData 16 i) := by
  classical
  by_cases hzero : oddKernel C=⊥
  · exact SixteenPointSemanticAlternatingZeroOddRecognition.pair_or_source i C rho pi hpi
      hlinear pointChart hpoint hzero heven A E j hj hMN hZmud lit family
  · letI : Finite A := Finite.of_injective j hj
    exact Or.inr ⟨SixteenPointSemanticAlternatingNonzeroOddActualSource.source i C hzero heven
      pi hpi A E j hj hMN hZmud lit family⟩

end SymmetricSubgroupAsymptotics.SixteenPointSemanticAlternatingActualRecognition
