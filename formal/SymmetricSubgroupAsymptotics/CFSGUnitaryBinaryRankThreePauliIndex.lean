import SymmetricSubgroupAsymptotics.CFSGUnitaryBinaryRankThreePauliEmbedding
import SymmetricSubgroupAsymptotics.QuaternaryPauliFourierPhaseNormalization
import SymmetricSubgroupAsymptotics.TernaryHeisenbergCompatibleNormalizerIndex

/-! The SAME Pauli27 with its Fourier and phase normalizers gives an
actual proper-index27 obstruction in the original order-two rank-three
unitary model. No order or splitting hypothesis is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGUnitaryBinaryRankThreePauliIndex
open CFSGTwistedAUnitaryCoordinates

private theorem map_conjugacy {A B : Type*} [Group A] [Group B]
    (f : A →* B) (x y z : A) (h : x*y*x⁻¹=z) : f x*f y*(f x)⁻¹=f z := by
  simpa only [map_mul,map_inv] using congrArg f h

theorem proper_index_ge_twentySeven (q : CFSG.PrimePower) (hq : q.order=2)
    [IsSimpleGroup (CFSG.Models.TwistedA 3 q)]
    (H : Subgroup (CFSG.Models.TwistedA 3 q)) (hH : H≠⊤) : 27≤H.index := by
  letI : Finite (CFSG.Models.TwistedA 3 q) :=
    Finite.of_surjective (unitaryProjectiveCover q 0) (unitaryProjectiveCover_surjective q 0)
  let f := (CFSGUnitaryBinaryRankThreePauliEmbedding.hom q hq).comp
    QuaternaryPauliUnitaryRepresentation.representation
  have hf : Function.Injective f := (CFSGUnitaryBinaryRankThreePauliEmbedding.hom_injective q hq).comp
    QuaternaryPauliUnitaryRepresentation.representation_injective
  apply TernaryHeisenbergCompatibleNormalizerIndex.proper_index_ge_twentySeven f hf
    (CFSGUnitaryBinaryRankThreePauliEmbedding.hom q hq QuaternaryPauliUnitaryRepresentation.fourier)
    (CFSGUnitaryBinaryRankThreePauliEmbedding.hom q hq QuaternaryPauliUnitaryRepresentation.phase)
    QuaternaryPauliFourierPhaseNormalization.rotation
    QuaternaryPauliFourierPhaseNormalization.shear ?_ ?_
    QuaternaryPauliFourierPhaseNormalization.rotation_coordinates
    QuaternaryPauliFourierPhaseNormalization.shear_coordinates H hH
  · intro h
    exact map_conjugacy (CFSGUnitaryBinaryRankThreePauliEmbedding.hom q hq) _ _ _
      (QuaternaryPauliFourierPhaseNormalization.fourier_normalizes h)
  · intro h
    exact map_conjugacy (CFSGUnitaryBinaryRankThreePauliEmbedding.hom q hq) _ _ _
      (QuaternaryPauliFourierPhaseNormalization.phase_normalizes h)

end SymmetricSubgroupAsymptotics.CFSGUnitaryBinaryRankThreePauliIndex
