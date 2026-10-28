import SymmetricSubgroupAsymptotics.CFSGSimpleProjectiveDescent
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Tactic.Group

/-! A central surjection onto a PERFECT target reflects the full centre.
The source need not be perfect. Perfectness of the target modulo its
centre is deliberately not used: that weaker condition is insufficient. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CentralSurjectionPerfectTargetCenter
variable {G H : Type*} [Group G] [Group H]

theorem preimage_center_le_center (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center G) [Group.IsPerfect H] :
    (Subgroup.center H).comap f ≤ Subgroup.center G := by
  intro g hg
  let c : G → G := fun x => g * x * g⁻¹ * x⁻¹
  have hc (x : G) : c x ∈ Subgroup.center G := by
    apply hker
    change f (g * x * g⁻¹ * x⁻¹) = 1
    have hh : Commute (f g) (f x) :=
      (Subgroup.mem_center_iff.mp hg (f x)).symm
    simpa only [map_mul, map_inv, commutatorElement_def] using hh.commutator_eq
  let chi : G →* Subgroup.center G := {
    toFun := fun x => ⟨c x, hc x⟩
    map_one' := by apply Subtype.ext; change g * 1 * g⁻¹ * 1⁻¹ = 1; group
    map_mul' := by
      intro x y
      apply Subtype.ext
      change c (x * y) = c x * c y
      have he : x * c y * x⁻¹ = c y := by
        rw [Subgroup.mem_center_iff.mp (hc y) x]
        group
      calc
        c (x * y) = c x * (x * c y * x⁻¹) := by dsimp only [c]; group
        _ = c x * c y := by rw [he] }
  letI : CommGroup (Subgroup.center G) :=
    { (inferInstance : Group (Subgroup.center G)) with
      mul_comm := fun x y => Subtype.ext
        ((Subgroup.mem_center_iff.mp x.property) y.val).symm }
  have hd : commutator G ≤ chi.ker := Abelianization.commutator_subset_ker chi
  have hm : (commutator G).map f = commutator H := by
    simp only [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective f hf]
  apply Subgroup.mem_center_iff.mpr
  intro x
  have hfx : f x ∈ (commutator G).map f := by
    rw [hm, Group.IsPerfect.commutator_eq_top]
    trivial
  obtain ⟨v, hv, hvx⟩ := hfx
  have hkv : x * v⁻¹ ∈ f.ker := by
    change f (x * v⁻¹) = 1
    rw [map_mul, map_inv, hvx, mul_inv_cancel]
  have hcv : chi v = 1 := hd hv
  have hcxv : chi (x * v⁻¹) = 1 := by
    apply Subtype.ext
    have hh : Commute g (x * v⁻¹) :=
      Subgroup.mem_center_iff.mp (hker hkv) g
    change g * (x * v⁻¹) * g⁻¹ * (x * v⁻¹)⁻¹ = 1
    simpa only [commutatorElement_def] using hh.commutator_eq
  have hcx : chi x = 1 := by
    rw [map_mul, map_inv, hcv, inv_one, mul_one] at hcxv
    exact hcxv
  have hx : g * x * g⁻¹ * x⁻¹ = 1 := congrArg Subtype.val hcx
  exact (commutatorElement_eq_one_iff_mul_comm.mp hx).symm

theorem preimage_center_eq_center (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center G) [Group.IsPerfect H] :
    (Subgroup.center H).comap f = Subgroup.center G := by
  apply le_antisymm (preimage_center_le_center f hf hker)
  intro x hx
  exact CFSGSimpleProjectiveDescent.map_mem_center f hf x hx

/-- The actual quotients by the FULL centres are equivalent, with no
source-perfectness or source-simple-projective hypothesis. -/
def projectiveEquiv (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center G) [Group.IsPerfect H] :
    G ⧸ Subgroup.center G ≃* H ⧸ Subgroup.center H := by
  let phi := (QuotientGroup.mk' (Subgroup.center H)).comp f
  have hphi : Function.Surjective phi :=
    (QuotientGroup.mk'_surjective (Subgroup.center H)).comp hf
  have hk : Subgroup.center G = phi.ker := by
    ext x
    change x ∈ Subgroup.center G ↔
      (QuotientGroup.mk' (Subgroup.center H)) (f x) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (SetLike.ext_iff.mp (preimage_center_eq_center f hf hker) x).symm
  exact QuotientGroup.liftEquiv (N := Subgroup.center G) hphi hk

end SymmetricSubgroupAsymptotics.CentralSurjectionPerfectTargetCenter
