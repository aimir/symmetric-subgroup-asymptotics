import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexR11Frame
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexIsometryNeighborCount
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveSpace

/-! Every actual original D R11 pair in rank>=5 has more common
neighbours than the disjoint-plane bound (q+1)^2. The proof transports
the explicit q^4 corrected chart through an actual original D word.
Rank four is deliberately absent: its triality obstruction is separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexR11LowerCount
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexR11Frame CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexResidualNeighborCount CFSGOrthogonalDIndexIsometryNeighborCount
open CFSGOrthogonalDIndexResidualChart
variable (K : Type) [Field K] [Finite K]

theorem fourth_power_le_R11_common_neighbors (s : ℕ)
    (P Q : Submodule K (Index (s + 5) → K))
    (hP : Module.finrank K P = 2) (hQ : Module.finrank K Q = 2)
    (hPs : ∀ x ∈ P, splitQuadraticForm K (s + 5) x = 0)
    (hQs : ∀ x ∈ Q, splitQuadraticForm K (s + 5) x = 0)
    (hmeet : P ⊓ Q ≠ ⊥)
    (hnonsingular : ¬∀ x ∈ P ⊔ Q, splitQuadraticForm K (s + 5) x = 0) :
    Nat.card K ^ 4 ≤ Nat.card (CommonNeighborPlanes K (s + 5) P Q) := by
  obtain ⟨g, w, hPm, hQm, hws, hwu, hw⟩ :=
    exists_normalized_frame K s P Q hP hQ hPs hQs hmeet hnonsingular
  let e := naturalLinearHom K (s + 5) g
  have he : ∀ x, splitQuadraticForm K (s + 5) (e x) = splitQuadraticForm K (s + 5) x :=
    naturalLinearHom_preserves_Q K (s + 1) g
  have heL : e.toLinearMap = Matrix.mulVecLin (g.val : Mat K (s + 5)) := by
    apply LinearMap.ext
    intro x
    rfl
  have hc := isometry_common_neighbors_card K (s + 5) e he P Q
  rw [heL, hPm, hQm] at hc
  exact (fourth_power_le_normalized_common_neighbors K s w hws hwu hw).trans_eq hc

theorem R11_common_neighbors_gt_disjoint_bound (s : ℕ)
    (P Q : Submodule K (Index (s + 5) → K))
    (hP : Module.finrank K P = 2) (hQ : Module.finrank K Q = 2)
    (hPs : ∀ x ∈ P, splitQuadraticForm K (s + 5) x = 0)
    (hQs : ∀ x ∈ Q, splitQuadraticForm K (s + 5) x = 0)
    (hdim : Module.finrank K ↥(P ⊓ Q) = 1)
    (hnonsingular : ¬∀ x ∈ P ⊔ Q, splitQuadraticForm K (s + 5) x = 0) :
    (Nat.card K + 1) ^ 2 < Nat.card (CommonNeighborPlanes K (s + 5) P Q) := by
  have hmeet : P ⊓ Q ≠ ⊥ := by
    intro he
    have hh := congrArg (fun S : Submodule K (Index (s + 5) → K) => Module.finrank K S) he
    change Module.finrank K ↥(P ⊓ Q) =
      Module.finrank K (⊥ : Submodule K (Index (s + 5) → K)) at hh
    rw [hdim, finrank_bot] at hh
    omega
  have htwo : 2 ≤ Nat.card K :=
    Nat.succ_le_of_lt (Finite.one_lt_card_iff_nontrivial.mpr inferInstance)
  exact (fourth_power_gt_disjoint_bound (Nat.card K) htwo).trans_le
    (fourth_power_le_R11_common_neighbors K s P Q hP hQ hPs hQs hmeet hnonsingular)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexR11LowerCount
