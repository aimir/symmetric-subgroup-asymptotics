import SymmetricSubgroupAsymptotics.CFSGSymplecticCoxeterMonomial
import SymmetricSubgroupAsymptotics.CFSGMonomialUnitRootAction
import SymmetricSubgroupAsymptotics.CFSGSymplecticTerminalTorus

/-! Two actual coordinate tori in the original elementary C group.
Both are conjugates of the already constructed terminal root word.
No independent membership or classical-group recognition is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

/-- The positive and negative weights on one original coordinate pair. -/
def coordinateTorusDiagonal (K : Type) [Field K] (r : ℕ) (i : Fin (r + 1))
    (g : Kˣ) : Index (r + 1) → K := fun x =>
  if x = Sum.inl i then (g : K) else if x = Sum.inr i then (g : K)⁻¹ else 1

def firstTorus (K : Type) [Field K] (r : ℕ) (g : Kˣ) : elementaryRootGroup K (r + 1) :=
  coxeterWeyl K r * terminalTorus K r g⁻¹ * (coxeterWeyl K r)⁻¹

def secondTorus (K : Type) [Field K] (r : ℕ) (g : Kˣ) : elementaryRootGroup K (r + 1) :=
  coxeterWeyl K r * firstTorus K r g * (coxeterWeyl K r)⁻¹

theorem firstTorus_coe (K : Type) [Field K] (r : ℕ) (g : Kˣ) :
    ((firstTorus K r g).val : Mat K (r + 1)) =
      Matrix.diagonal (coordinateTorusDiagonal K r 0 g) := by
  change ((coxeterWeyl K r).val : Mat K (r + 1)) *
    ((terminalTorus K r g⁻¹).val : Mat K (r + 1)) *
    (↑((coxeterWeyl K r).val⁻¹) : Mat K (r + 1)) = _
  rw [terminalTorus_coe]
  rw [CFSGMonomialUnitRootAction.monomial_conjugation_diagonal
    (coxeterWeyl K r).val (coxeterCycle r).symm
    (coxeterSign K r ∘ (coxeterCycle r).symm) _ (coxeterWeyl_monomial K r)]
  congr 1
  funext x
  simp only [Function.comp_apply, Equiv.symm_apply_eq, coxeterCycle_inl_last,
    coxeterCycle_inr_last, Units.val_inv_eq_inv_val, inv_inv, coordinateTorusDiagonal]
  by_cases hp : x = Sum.inl (0 : Fin (r + 1)) <;>
    by_cases hn : x = Sum.inr (0 : Fin (r + 1)) <;> simp_all

theorem secondTorus_coe (K : Type) [Field K] (r : ℕ) (hr : 0 < r) (g : Kˣ) :
    ((secondTorus K r g).val : Mat K (r + 1)) =
      Matrix.diagonal (coordinateTorusDiagonal K r (⟨1, by omega⟩ : Fin (r + 1)) g) := by
  change ((coxeterWeyl K r).val : Mat K (r + 1)) *
    ((firstTorus K r g).val : Mat K (r + 1)) *
    (↑((coxeterWeyl K r).val⁻¹) : Mat K (r + 1)) = _
  rw [firstTorus_coe]
  rw [CFSGMonomialUnitRootAction.monomial_conjugation_diagonal
    (coxeterWeyl K r).val (coxeterCycle r).symm
    (coxeterSign K r ∘ (coxeterCycle r).symm) _ (coxeterWeyl_monomial K r)]
  congr 1
  funext x
  have hp : coxeterCycle r (Sum.inl (0 : Fin (r + 1))) =
      Sum.inl (⟨1, Nat.succ_lt_succ hr⟩ : Fin (r + 1)) := coxeterCycle_inl_of_lt r 0 hr
  have hn : coxeterCycle r (Sum.inr (0 : Fin (r + 1))) =
      Sum.inr (⟨1, Nat.succ_lt_succ hr⟩ : Fin (r + 1)) := coxeterCycle_inr_of_lt r 0 hr
  simp only [Function.comp_apply, coordinateTorusDiagonal, Equiv.symm_apply_eq, hp, hn]

/-- The first two pairs have the same actual torus parameter. This
fixes the first short root and scales the second long root by its square. -/
def initialTorus (K : Type) [Field K] (r : ℕ) (g : Kˣ) : elementaryRootGroup K (r + 1) :=
  firstTorus K r g * secondTorus K r g

theorem initialTorus_coe (K : Type) [Field K] (r : ℕ) (hr : 0 < r) (g : Kˣ) :
    ((initialTorus K r g).val : Mat K (r + 1)) =
      Matrix.diagonal (fun x => coordinateTorusDiagonal K r 0 g x *
        coordinateTorusDiagonal K r (⟨1, by omega⟩ : Fin (r + 1)) g x) := by
  change ((firstTorus K r g).val : Mat K (r + 1)) *
    ((secondTorus K r g).val : Mat K (r + 1)) = _
  rw [firstTorus_coe, secondTorus_coe K r hr, Matrix.diagonal_mul_diagonal]

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
