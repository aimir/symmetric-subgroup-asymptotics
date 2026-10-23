import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingHom
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelFactorization
import Mathlib.Tactic.Group

/-! Nonzero simple leading coordinates survive conjugation by the
literal Borel envelope: its U factor acts trivially on leading
coordinates, and its actual diagonal torus factor scales matrix entries
by units. No torus-character separation is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRegularLeadingBorel
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckColumns
open CFSGNormTwoCoordinateLeadingFactor CFSGNormTwoCoordinateLeadingHom
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoGeckBorelFactorization
open CFSGDiagonalMatrixUnits
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
private abbrev Mat (K : Type) := Matrix ((b₀).support ⊕ Roots A) ((b₀).support ⊕ Roots A) K

theorem positive_conjugate_leading (K : Type) [Field K]
    (a u : (Mat A hd hs hp ho K)ˣ)
    (ha : a ∈ rootGroup A hs hp b₀ s₀ K false)
    (hu : u ∈ rootGroup A hs hp b₀ s₀ K false) :
    leadingCoordinates A hd hs hp ho K (a⁻¹ * u * a) =
      leadingCoordinates A hd hs hp ho K u := by
  let a' : rootGroup A hs hp b₀ s₀ K false := ⟨a, ha⟩
  let u' : rootGroup A hs hp b₀ s₀ K false := ⟨u, hu⟩
  have he : leadingHom A hd hs hp ho K (a'⁻¹ * u' * a') =
      leadingHom A hd hs hp ho K u' := by
    simp [map_mul, map_inv, mul_comm, mul_left_comm, mul_assoc]
  exact congrArg (fun c : Multiplicative (Fin r → K) => c.toAdd) he

theorem diagonal_conjugate_leading_ne_zero (K : Type) [Field K]
    (d : (b₀).support ⊕ Roots A → Kˣ) (u : (Mat A hd hs hp ho K)ˣ) (i : Fin r)
    (hu : leadingCoordinates A hd hs hp ho K u i ≠ 0) :
    leadingCoordinates A hd hs hp ho K
      ((diagonalHom ((b₀).support ⊕ Roots A) K d)⁻¹ * u *
        diagonalHom ((b₀).support ⊕ Roots A) K d) i ≠ 0 := by
  rw [← map_inv]
  change (((diagonalHom ((b₀).support ⊕ Roots A) K (d⁻¹) : Mat A hd hs hp ho K) *
    (u : Mat A hd hs hp ho K)) *
    (diagonalHom ((b₀).support ⊕ Roots A) K d : Mat A hd hs hp ho K))
      (Sum.inl (s₀ i)) (Sum.inr (negativeIndex A hs hp (s₀ i))) ≠ 0
  simp only [diagonalHom_val, Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact mul_ne_zero (mul_ne_zero (Units.ne_zero ((d (Sum.inl (s₀ i)))⁻¹)) hu)
    (Units.ne_zero (d (Sum.inr (negativeIndex A hs hp (s₀ i)))))

theorem borel_conjugate_regular (K : Type) [Field K]
    (b u : (Mat A hd hs hp ho K)ˣ)
    (hb : b ∈ borelEnvelope A hs hp b₀ s₀ K)
    (hu : u ∈ rootGroup A hs hp b₀ s₀ K false)
    (hreg : ∀ i, leadingCoordinates A hd hs hp ho K u i ≠ 0) :
    ∀ i, leadingCoordinates A hd hs hp ho K (b⁻¹ * u * b) i ≠ 0 := by
  obtain ⟨a, ha, t, ht, hb'⟩ := borel_factor A hs hp b₀ s₀ K b hb
  obtain ⟨d, hd'⟩ := torusGroup_le_diagonal A hs hp b₀ s₀ K ht
  have he : b⁻¹ * u * b = t⁻¹ * (a⁻¹ * u * a) * t := by rw [hb']; group
  intro i
  rw [he, ← hd']
  apply diagonal_conjugate_leading_ne_zero A hd hs hp ho K d (a⁻¹ * u * a) i
  rw [positive_conjugate_leading A hd hs hp ho K a u ha hu]
  exact hreg i

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRegularLeadingBorel
