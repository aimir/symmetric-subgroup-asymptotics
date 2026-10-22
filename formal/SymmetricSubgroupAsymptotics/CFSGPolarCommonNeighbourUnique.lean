import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! If disjoint two-planes each have a unique point orthogonal to the
other, every common polar-line neighbour is their forced-point join.
This is literal submodule geometry, without a polar-space census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPolarCommonNeighbourUnique
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem common_neighbour_eq_forced_sum (B : LinearMap.BilinForm K V)
    (P Q R : Submodule K V) (hPQ : Disjoint P Q)
    (hPa : Module.finrank K (P ⊓ B.orthogonal Q : Submodule K V) = 1)
    (hQa : Module.finrank K (Q ⊓ B.orthogonal P : Submodule K V) = 1)
    (hR : Module.finrank K R = 2)
    (hPR : Module.finrank K (P ⊓ R : Submodule K V) = 1)
    (hQR : Module.finrank K (Q ⊓ R : Submodule K V) = 1)
    (hcrossP : ∀ p ∈ P, ∀ r ∈ R, B p r = 0)
    (hcrossQ : ∀ q ∈ Q, ∀ r ∈ R, B q r = 0) :
    R = (P ⊓ B.orthogonal Q) ⊔ (Q ⊓ B.orthogonal P) := by
  let X : Submodule K V := P ⊓ R
  let Y : Submodule K V := Q ⊓ R
  let A : Submodule K V := P ⊓ B.orthogonal Q
  let C : Submodule K V := Q ⊓ B.orthogonal P
  have hXd : Module.finrank K X = 1 := hPR
  have hYd : Module.finrank K Y = 1 := hQR
  have hAd : Module.finrank K A = 1 := hPa
  have hCd : Module.finrank K C = 1 := hQa
  have hXA : X ≤ A := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    intro q hq
    exact hcrossQ q hq x hx.2
  have hYC : Y ≤ C := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    intro p hp
    exact hcrossP p hp y hy.2
  have hX : X = A := Submodule.eq_of_le_of_finrank_le hXA (by rw [hAd, hXd])
  have hY : Y = C := Submodule.eq_of_le_of_finrank_le hYC (by rw [hCd, hYd])
  have hd : Disjoint X Y := hPQ.mono (show X ≤ P from inf_le_left) (show Y ≤ Q from inf_le_left)
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq X Y
  rw [hd.eq_bot, finrank_bot, hXd, hYd, add_zero] at hdim
  have hsum : Module.finrank K (X ⊔ Y : Submodule K V) = 2 := by omega
  have hle : X ⊔ Y ≤ R := sup_le inf_le_right inf_le_right
  have he : X ⊔ Y = R := Submodule.eq_of_le_of_finrank_le hle (by rw [hR, hsum])
  calc
    R = X ⊔ Y := he.symm
    _ = A ⊔ C := by rw [hX, hY]

end SymmetricSubgroupAsymptotics.CFSGPolarCommonNeighbourUnique
