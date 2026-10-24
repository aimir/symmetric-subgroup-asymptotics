import SymmetricSubgroupAsymptotics.CFSGFFourBinaryCentralCoordinateWords
import SymmetricSubgroupAsymptotics.CFSGFFourBinaryLongLeviCentralPair

/-! A first actual Levi covariance identity on the literal seven central
coordinates. The quadratic correction is obtained from the checked root
word calculation, with no proposed module action used as a premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryLongLeviCentralCoordinates
open CFSGFFourBinaryCentralCoordinateWords CFSGFFourBinaryRadicalCentralLayers
open CFSGFFourBinaryFixedRadicalEmbedding CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix
open CFSGFFourE6HeisenbergLeviRoots CFSGTwistedE6HeisenbergStableRootFamilies

private theorem central_parts (K : Type) [Field K] [CharP K 2]
    (c : K) (u v : Fin 3 → K) :
    centralMatrixHom K (Multiplicative.ofAdd (c,(u,v))) =
      centralMatrixHom K (Multiplicative.ofAdd (0,(u,0))) *
      centralMatrixHom K (Multiplicative.ofAdd (0,(0,v))) *
      centralMatrixHom K (Multiplicative.ofAdd (c,(0 : Extra K))) := by
  have he : (Multiplicative.ofAdd (c,(u,v)) : CentralCoordinates K) =
      Multiplicative.ofAdd (0,(u,0)) * Multiplicative.ofAdd (0,(0,v)) *
        Multiplicative.ofAdd (c,(0 : Extra K)) := by
    apply Multiplicative.toAdd.injective
    change (c,(u,v)) = ((0,(u,0))+(0,(0,v)))+(c,(0,0))
    apply Prod.ext
    · simp
    · apply Prod.ext <;> simp
  rw [he,map_mul,map_mul]

theorem long_positive_central_first (K : Type) [Field K] [CharP K 2] (a t : K) :
    canonicalRoot realizationData K false 2 a *
        centralMatrixHom K (Multiplicative.ofAdd (0,(Pi.single (2 : Fin 3) t,0))) *
        (canonicalRoot realizationData K false 2 a)⁻¹ =
      centralMatrixHom K (Multiplicative.ofAdd
        (a*t^2,(Pi.single (2 : Fin 3) t,Pi.single (2 : Fin 3) (a*t)))) := by
  rw [central_first_word,central_parts,central_first_word,central_second_word,
    central_scalar_word]
  simpa [pairPick,partner,mul_assoc] using
    CFSGFFourBinaryLongLeviCentralPair.long_positive_conjugate_pair K a t

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryLongLeviCentralCoordinates
