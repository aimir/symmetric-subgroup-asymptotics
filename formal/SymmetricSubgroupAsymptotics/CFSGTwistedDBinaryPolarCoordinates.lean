import SymmetricSubgroupAsymptotics.CFSGTwistedDBinaryNormPlaneCoordinates
import SymmetricSubgroupAsymptotics.SymplecticLastPairCoordinates

/-! Actual fixed-space coordinates retain the untouched hyperbolic
strings and replace the literal norm-plane coordinate by its proved
trace-one pair. Their polar pairing is the native symplectic pairing.
The quadratic form itself and its original isometry group are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGTwistedDBinaryPolarCoordinates
open CFSGTwistedDLinearParameters CFSGTwistedDFixedQuadraticSpace
open CFSGTwistedDFixedVectorParametrization CFSGTwistedA2FixedField
open CFSGTwistedDAnisotropicNormForm CFSGTwistedDBinaryNormPlaneCoordinates

def parameterPairEquiv (n : ℕ) (q : CFSG.PrimePower) (hq : q.prime = 2) :
    ((Fin (n+1) → fixedField q) × ((Fin (n+1) → fixedField q) × q.Extension 2)) ≃ₗ[fixedField q]
      ((Fin (n+1) → fixedField q) × ((Fin (n+1) → fixedField q) ×
        (fixedField q × fixedField q))) :=
  LinearEquiv.prodCongr (LinearEquiv.refl (fixedField q) _)
    (LinearEquiv.prodCongr (LinearEquiv.refl (fixedField q) _) (pairEquiv q hq).symm)

def spaceEquiv (n : ℕ) (q : CFSG.PrimePower) (hq : q.prime = 2) :
    fixedSpace n q ≃ₗ[fixedField q]
      (CFSGSymplecticSerreMatrices.Index (n+2) → fixedField q) :=
  ((linearParameters n q).trans (parameterPairEquiv n q hq)).trans
    (SymplecticLastPairCoordinates.appendEquiv (fixedField q) (n+1))

theorem polar_parameters (n : ℕ) (q : CFSG.PrimePower) (v w : fixedSpace n q) :
    (fixedQuadraticForm n q).polarBilin v w =
      (∑ i : Fin (n+1), ((linearParameters n q v).1 i * (linearParameters n q w).2.1 i +
        (linearParameters n q w).1 i * (linearParameters n q v).2.1 i)) +
      (normForm q).polarBilin (linearParameters n q v).2.2 (linearParameters n q w).2.2 := by
  let P := linearParameters n q
  have hQ (z : fixedSpace n q) : fixedQuadraticForm n q z =
      (∑ i : Fin (n+1), (P z).1 i * (P z).2.1 i) +
        Algebra.norm (fixedField q) (P z).2.2 := by
    have h := quadratic_parameters n q (P z)
    change fixedQuadraticForm n q (P.symm (P z)) = _ at h
    rw [P.symm_apply_apply] at h
    exact h
  change fixedQuadraticForm n q (v+w) - fixedQuadraticForm n q v -
    fixedQuadraticForm n q w = _
  rw [hQ (v+w), hQ v, hQ w]
  change _ = (∑ i : Fin (n+1), ((P v).1 i*(P w).2.1 i+(P w).1 i*(P v).2.1 i)) +
    (normForm q).polarBilin (P v).2.2 (P w).2.2
  simp only [map_add, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  rw [QuadraticMap.polarBilin_apply_apply]
  simp only [QuadraticMap.polar, normForm_apply, add_mul, mul_add, Finset.sum_add_distrib]
  ring

theorem spaceEquiv_preserves (n : ℕ) (q : CFSG.PrimePower) (hq : q.prime = 2)
    (v w : fixedSpace n q) :
    CFSGSymplecticNaturalBilinearClassGeometry.naturalPairing (fixedField q) (n+2)
      (spaceEquiv n q hq v) (spaceEquiv n q hq w) =
        (fixedQuadraticForm n q).polarBilin v w := by
  letI : CharP (fixedField q) 2 := Eq.mp
    (congrArg (fun p : ℕ => CharP (fixedField q) p) hq)
    (inferInstance : CharP (fixedField q) q.prime)
  let P := linearParameters n q
  let z := (pairEquiv q hq).symm (P v).2.2
  let t := (pairEquiv q hq).symm (P w).2.2
  have hn : (normForm q).polarBilin (P v).2.2 (P w).2.2 = z.1*t.2+z.2*t.1 := by
    have h := pair_polar q hq z t
    change (normForm q).polarBilin
      (pairEquiv q hq ((pairEquiv q hq).symm (P v).2.2))
      (pairEquiv q hq ((pairEquiv q hq).symm (P w).2.2)) = z.1*t.2+z.2*t.1 at h
    rw [(pairEquiv q hq).apply_symm_apply, (pairEquiv q hq).apply_symm_apply] at h
    exact h
  have hv : spaceEquiv n q hq v = SymplecticLastPairCoordinates.appendEquiv
      (fixedField q) (n+1) ((P v).1, ((P v).2.1, z)) := rfl
  have hw : spaceEquiv n q hq w = SymplecticLastPairCoordinates.appendEquiv
      (fixedField q) (n+1) ((P w).1, ((P w).2.1, t)) := rfl
  rw [hv, hw, SymplecticLastPairCoordinates.pairing_append, polar_parameters]
  change _ = (∑ i : Fin (n+1), ((P v).1 i*(P w).2.1 i+(P w).1 i*(P v).2.1 i)) +
    (normForm q).polarBilin (P v).2.2 (P w).2.2
  rw [hn]
  change (∑ i : Fin (n+1), ((P v).1 i*(P w).2.1 i-(P v).2.1 i*(P w).1 i)) +
      (z.1*t.2-z.2*t.1) =
    (∑ i : Fin (n+1), ((P v).1 i*(P w).2.1 i+(P w).1 i*(P v).2.1 i)) +
      (z.1*t.2+z.2*t.1)
  apply congrArg₂ (fun a b : fixedField q => a+b)
  · apply Finset.sum_congr rfl
    intro i _
    rw [CharTwo.sub_eq_add]
    ring
  · exact CharTwo.sub_eq_add _ _

end SymmetricSubgroupAsymptotics.CFSGTwistedDBinaryPolarCoordinates
