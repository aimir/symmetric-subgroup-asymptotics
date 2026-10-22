import SymmetricSubgroupAsymptotics.CFSGTwistedA2DiagonalTorus
import SymmetricSubgroupAsymptotics.CFSGTwistedA2HighestFixedRoots
import SymmetricSubgroupAsymptotics.CFSGTwistedAPairedFixedRoots

/-! The actual two-root diagonal word is fixed by the literal signed
field/diagram twist when σ²=1. Thus it gives an ORIGINAL fixed-source
torus element, before any derived-subgroup or Sylow assertion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2DiagonalTorus
open CFSGTwistedANaturalMatrices CFSGTwistedA2OriginalRelations
variable (K : Type) [Field K]

theorem signedReversal_conjugate_diagonal (D : Fin 3 → K) :
    (signedReversalUnit K 2 : Mat K 2) * Matrix.diagonal D *
      (↑((signedReversalUnit K 2)⁻¹) : Mat K 2) = Matrix.diagonal (fun i => D i.rev) := by
  let J := signedReversalUnit K 2
  have hm := CFSGTypeAMonomialMatrices.monomial_mul_diagonal
    Fin.revPerm (signWeight K 2) D
  rw [← signedReversalUnit_monomial] at hm
  change (J : Mat K 2) * Matrix.diagonal D =
    Matrix.diagonal (fun i => D i.rev) * (J : Mat K 2) at hm
  calc
    _ = Matrix.diagonal (fun i => D i.rev) *
        ((J : Mat K 2) * (↑(J⁻¹) : Mat K 2)) := by rw [hm, mul_assoc]
    _ = _ := by rw [Units.mul_inv, mul_one]

theorem torusUnit_fixed (σ : K ≃+* K) (hσ : Function.Involutive σ)
    (z : K) (hz : z ≠ 0) :
    diagramFieldUnitHom K 2 σ.toRingHom (torusUnit K σ z hz) = torusUnit K σ z hz := by
  apply Units.ext
  rw [diagramFieldUnitHom_val]
  change (signedReversalUnit K 2 : Mat K 2) *
    (σ.toRingHom.mapMatrix (Matrix.diagonal (torusInverseWeights K σ z))).transpose *
      (↑((signedReversalUnit K 2)⁻¹) : Mat K 2) = Matrix.diagonal (torusWeights K σ z)
  have hm : σ.toRingHom.mapMatrix (Matrix.diagonal (torusInverseWeights K σ z)) =
      Matrix.diagonal (fun i => σ (torusInverseWeights K σ z i)) := by
    ext i j
    change σ (if i = j then torusInverseWeights K σ z i else 0) =
      if i = j then σ (torusInverseWeights K σ z i) else 0
    by_cases h : i = j <;> simp only [h, if_true, if_false, map_zero]
  rw [hm, Matrix.diagonal_transpose, signedReversal_conjugate_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  fin_cases i <;> simp [torusWeights, torusInverseWeights, Fin.rev, map_div₀, map_inv₀, hσ z]

theorem torusNatural_fixed (σ : K ≃+* K) (hσ : Function.Involutive σ)
    (z : K) (hz : z ≠ 0) :
    diagramFieldUnitHom K 2 σ.toRingHom (torusNatural K σ z).val = (torusNatural K σ z).val := by
  rw [torusNatural_unit K σ z hz]
  exact torusUnit_fixed K σ hσ z hz

def originalTorus (q : CFSG.PrimePower) (z : q.Extension 2) (hz : z ≠ 0) :
    CFSG.Models.Chevalley.fixedSubgroup A (q.Extension 2)
      CFSG.Models.reverseNode (fun _ => q.order) :=
  fixedElementOfNaturalUnit q
    (torusNatural (q.Extension 2) (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2) z)
    (torusNatural_fixed (q.Extension 2) (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2)
      (fun x => extension_two_pow_twice q x) z hz)

end SymmetricSubgroupAsymptotics.CFSGTwistedA2DiagonalTorus
