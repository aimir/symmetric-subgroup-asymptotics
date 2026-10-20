import SymmetricSubgroupAsymptotics.SixteenPointSemanticAlternatingZeroOddActualSource

/-! Honest recognition cover for the whole zero-odd quartet branch:
the original eight-pair geometry is retained as an explicit alternative. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixteenPointSemanticAlternatingZeroOddRecognition
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
    (hzero : oddKernel C=⊥)
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
  by_cases hp : Nonempty (BinaryPairFrame (preE7NonPairAction 16 i) (Fin 8))
  · exact Or.inl hp
  · exact Or.inr ⟨SixteenPointSemanticAlternatingZeroOddActualSource.source i C rho pi hpi
      hlinear pointChart hpoint hzero heven hp A E j hj hMN hZmud lit family⟩

end SymmetricSubgroupAsymptotics.SixteenPointSemanticAlternatingZeroOddRecognition
