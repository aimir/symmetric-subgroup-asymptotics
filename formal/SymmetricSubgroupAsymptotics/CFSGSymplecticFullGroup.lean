import SymmetricSubgroupAsymptotics.CFSGSymplecticEliminationStep
import SymmetricSubgroupAsymptotics.CFSGSymplecticRankOneGeneration

/-! The literal original elementary C matrices are the full natural
symplectic group, over every field and in every rank. The proof uses
Gaussian elimination at rank one and actual hyperbolic-pair stabilizers
for induction; no classical-group recognition theorem is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticStabilizerCoordinates
open CFSGSymplecticSerreMatrices
variable (K : Type) [Field K]

theorem all_formPreserving_elementary (n : ℕ) (u : (Mat K n)ˣ)
    (hu : PreservesPairing n (u : Mat K n)) : u ∈ elementaryRootGroup K n := by
  induction n with
  | zero =>
    have he : u = 1 := by
      apply Units.ext
      ext i j
      cases i <;> exact Fin.elim0 ‹Fin 0›
    rw [he]
    exact (elementaryRootGroup K 0).one_mem
  | succ n ih =>
    cases n with
    | zero => exact rankOne_formPreserving_mem K u hu
    | succ r =>
      exact all_formPreserving_elementary_step K (r + 1) (by omega)
        (fun v hv => ih v hv) u hu

theorem elementaryRootGroup_eq_formPreserving (n : ℕ) :
    elementaryRootGroup K n = formPreservingUnits K n := by
  apply le_antisymm (elementaryRootGroup_le_formPreserving K n)
  intro u hu
  exact all_formPreserving_elementary K n u (preservesPairing_of_form n _ hu)

theorem elementaryToSymplectic_surjective (n : ℕ) :
    Function.Surjective (elementaryToSymplectic K n) := by
  intro g
  let u : (Mat K n)ˣ := {
    val := g.val
    inv := (g⁻¹).val
    val_inv := congrArg Subtype.val (mul_inv_cancel g)
    inv_val := congrArg Subtype.val (inv_mul_cancel g) }
  refine ⟨⟨u, all_formPreserving_elementary K n u (preservesPairing_of_form n _ g.property)⟩, ?_⟩
  apply Subtype.ext
  rfl

def elementarySymplecticEquiv (n : ℕ) :
    elementaryRootGroup K n ≃* Matrix.symplecticGroup (Fin n) K :=
  MulEquiv.ofBijective (elementaryToSymplectic K n)
    ⟨elementaryToSymplectic_injective K n, elementaryToSymplectic_surjective K n⟩

end SymmetricSubgroupAsymptotics.CFSGSymplecticStabilizerCoordinates
