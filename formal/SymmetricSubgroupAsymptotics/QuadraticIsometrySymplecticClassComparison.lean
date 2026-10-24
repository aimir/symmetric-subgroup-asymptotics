import SymmetricSubgroupAsymptotics.BilinearPreserverCoordinateEquivalence
import SymmetricSubgroupAsymptotics.EquivariantStabilizerEquivalence
import SymmetricSubgroupAsymptotics.CFSGSymplecticPolarEquivalence
import Mathlib.Algebra.Group.ConjFinite

/-! Actual polar coordinates transport the quadratic-refinement class
comparison to the SAME native symplectic group and its SAME chosen
first-vector stabilizer. Applications must prove the literal pairing
identity for E; no isometry-group recognition or class-count premise is
hidden in this transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.QuadraticIsometrySymplecticClassComparison
open QuadraticIsometryPolarStabilizer BilinearPreserverCoordinateEquivalence
open CFSGSymplecticSerreMatrices CFSGSymplecticPointAffineHom
open CFSGSymplecticNaturalBilinearClassGeometry CFSGSymplecticPolarEquivalence
variable (K : Type) [Field K] {V : Type*} [AddCommGroup V] [Module K V]

local instance finiteElementary [Finite K] (r : ℕ) : Finite (elementaryRootGroup K r) :=
  Finite.of_injective (fun g : elementaryRootGroup K r => (g.val : Mat K r))
    (by intro g h he; exact Subtype.ext (Units.ext he))

def polarElementaryEquiv (r : ℕ) (Q : QuadraticForm K V)
    (E : V ≃ₗ[K] (Index (r+1) → K))
    (hE : ∀ x y, naturalPairing K (r+1) (E x) (E y) = Q.polarBilin x y) :
    polarPreservers Q.polarBilin ≃* elementaryRootGroup K (r+1) :=
  (preserverEquiv Q.polarBilin (naturalPairing K (r+1)) E hE).trans
    (elementaryPolarEquiv K (r+1)).symm

theorem polarElementaryEquiv_equivariant (r : ℕ) (Q : QuadraticForm K V)
    (E : V ≃ₗ[K] (Index (r+1) → K))
    (hE : ∀ x y, naturalPairing K (r+1) (E x) (E y) = Q.polarBilin x y)
    (g : polarPreservers Q.polarBilin) (v : V) :
    E (g.val v) = naturalLinearHom K (r+1) (polarElementaryEquiv K r Q E hE g) (E v) := by
  let a := preserverEquiv Q.polarBilin (naturalPairing K (r+1)) E hE g
  have he := congrArg Subtype.val ((elementaryPolarEquiv K (r+1)).apply_symm_apply a)
  have hv := congrArg (fun T : (Index (r+1) → K) ≃ₗ[K] (Index (r+1) → K) => T (E v)) he
  change naturalLinearHom K (r+1) (polarElementaryEquiv K r Q E hE g) (E v) =
    E (g.val (E.symm (E v))) at hv
  rw [E.symm_apply_apply] at hv
  exact hv.symm

theorem class_card_le [Finite K] [Finite V] [CharP K 2]
    (hK : Nat.card K = 2) (r : ℕ) (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate)
    (E : V ≃ₗ[K] (Index (r+1) → K))
    (hE : ∀ x y, naturalPairing K (r+1) (E x) (E y) = Q.polarBilin x y) :
    Nat.card (ConjClasses (CFSGOrthogonalDIndexSingularComponents.isometryGroup Q)) ≤
      Nat.card (ConjClasses (elementaryRootGroup K (r+1))) +
        Nat.card (ConjClasses (pointStabilizer K r)) := by
  letI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun T : V ≃ₗ[K] V => (T : V → V)) LinearEquiv.coe_injective
  let ρ := polarRepresentation Q
  letI := BilinearContragredientDuality.naturalAction ρ
  letI := BilinearContragredientDuality.naturalAction (naturalLinearHom K (r+1))
  let eG := polarElementaryEquiv K r Q E hE
  let e : Index (r+1) → K := Pi.single (Sum.inl 0) 1
  let v : V := E.symm e
  have he : e ≠ 0 := by
    intro hz
    have h := congrFun hz (Sum.inl 0)
    change (1 : K) = 0 at h
    exact one_ne_zero h
  have hcoord (g : polarPreservers Q.polarBilin) (x : V) :
      E (g • x) = eG g • E x := polarElementaryEquiv_equivariant K r Q E hE g x
  have ht (w : V) (hw : w ≠ 0) :
      ∃ g : polarPreservers Q.polarBilin, ρ g v = w := by
    have hwE : E w ≠ 0 := by
      intro hz
      exact hw (E.injective (hz.trans E.map_zero.symm))
    obtain ⟨g, hg⟩ := exists_map_nonzero K (r+1) (Nat.succ_pos r) e (E w) he hwE
    refine ⟨eG.symm g, ?_⟩
    apply E.injective
    change E ((eG.symm g).val v) = E w
    rw [polarElementaryEquiv_equivariant]
    change naturalLinearHom K (r+1) (eG (eG.symm g)) (E (E.symm e)) = E w
    rw [eG.apply_symm_apply, E.apply_symm_apply]
    exact hg
  have eP : MulAction.stabilizer (polarPreservers Q.polarBilin) v ≃*
      pointStabilizer K r := by
    have eP₀ := EquivariantStabilizerEquivalence.stabilizerEquiv eG E.toEquiv hcoord v
    change MulAction.stabilizer (polarPreservers Q.polarBilin) v ≃*
      MulAction.stabilizer (elementaryRootGroup K (r+1)) (E v) at eP₀
    have hEv : E v = e := E.apply_symm_apply e
    rw [hEv] at eP₀
    exact eP₀
  have hG : Nat.card (ConjClasses (polarPreservers Q.polarBilin)) ≤
      Nat.card (ConjClasses (elementaryRootGroup K (r+1))) :=
    Nat.card_le_card_of_surjective (ConjClasses.map eG.symm.toMonoidHom)
      (ConjClasses.map_surjective eG.symm.surjective)
  have hP : Nat.card (ConjClasses (MulAction.stabilizer (polarPreservers Q.polarBilin) v)) ≤
      Nat.card (ConjClasses (pointStabilizer K r)) :=
    Nat.card_le_card_of_surjective (ConjClasses.map eP.symm.toMonoidHom)
      (ConjClasses.map_surjective eP.symm.surjective)
  exact (QuadraticIsometryPolarStabilizer.class_card_le hK Q hQ v ht).trans
    (Nat.add_le_add hG hP)

end SymmetricSubgroupAsymptotics.QuadraticIsometrySymplecticClassComparison
