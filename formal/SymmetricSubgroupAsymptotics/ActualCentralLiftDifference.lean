import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! Differences of two lifts through an actual central kernel are genuine
homomorphisms into that SAME kernel. No section or split is chosen. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualCentralLiftDifference
variable {F K A : Type} [Group F] [Group K] [Group A]
  (q : K →* A) (hc : ∀ z : q.ker, ∀ k : K, (z : K)*k=k*(z : K))
  (psi : F →* K)

abbrev Lift := {phi : F →* K // q.comp phi=q.comp psi}

private theorem difference_mem (phi : Lift q psi) (x : F) :
    phi.val x * (psi x)⁻¹ ∈ q.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv]
  have h := DFunLike.congr_fun phi.property x
  change q (phi.val x)=q (psi x) at h
  rw [h, mul_inv_cancel]

/-- A reference lift identifies the actual fibre with a subset of central
characters; the reference is used only to bound that fibre. -/
def difference (phi : Lift q psi) : F →* q.ker where
  toFun x := ⟨phi.val x*(psi x)⁻¹,difference_mem q psi phi x⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by
    apply Subtype.ext
    change phi.val (x*y)*(psi (x*y))⁻¹ =
      (phi.val x*(psi x)⁻¹)*(phi.val y*(psi y)⁻¹)
    simp only [map_mul,mul_inv_rev]
    calc
      _ = phi.val x*((phi.val y*(psi y)⁻¹)*(psi x)⁻¹) := by simp only [mul_assoc]
      _ = phi.val x*((psi x)⁻¹*(phi.val y*(psi y)⁻¹)) := by
        rw [hc ⟨phi.val y*(psi y)⁻¹,difference_mem q psi phi y⟩ ((psi x)⁻¹)]
      _ = _ := by simp only [mul_assoc]

@[simp] theorem difference_apply (phi : Lift q psi) (x : F) :
    ((difference q hc psi phi x : q.ker) : K)=phi.val x*(psi x)⁻¹ := rfl

theorem difference_injective : Function.Injective (difference q hc psi) := by
  intro phi chi h
  apply Subtype.ext
  apply MonoidHom.ext
  intro x
  have hh := congrArg (fun f : F →* q.ker => ((f x : q.ker) : K)) h
  exact mul_right_cancel hh

variable (alpha : F → F) (beta : K ≃* K)
  (hpsi : ∀ x, psi (alpha x)=beta (psi x))
  (hfixed : ∀ z : q.ker, beta (z : K)=(z : K))

include hpsi hfixed in
theorem difference_invariant (phi : Lift q psi)
    (hphi : ∀ x, phi.val (alpha x)=beta (phi.val x)) (x : F) :
    difference q hc psi phi (alpha x)=difference q hc psi phi x := by
  apply Subtype.ext
  change phi.val (alpha x)*(psi (alpha x))⁻¹=phi.val x*(psi x)⁻¹
  rw [hphi,hpsi,← beta.map_inv,← beta.map_mul]
  exact hfixed ⟨phi.val x*(psi x)⁻¹,difference_mem q psi phi x⟩
end SymmetricSubgroupAsymptotics.ActualCentralLiftDifference
