import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! Narrow Apache-2.0 adaptation of AxiomMath/CFSG69cb972f,
Dihedral/Glauberman/DicksonMaxExist.lean31–125. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CyclicInversionDihedralEquivalence
open Multiplicative
theorem nonempty_sup_zpowers_mulEquiv_dihedral {G : Type*} [Group G] (C : Subgroup G)
    (hC : IsCyclic C) (w : G) (hw : w ∉ C) (hw2 : w * w = 1)
    (hinv : ∀ c ∈ C, w * c * w⁻¹ = c⁻¹) :
    Nonempty ((C ⊔ Subgroup.zpowers w : Subgroup G) ≃* DihedralGroup (Nat.card C)) := by
  classical
  let e : Multiplicative (ZMod (Nat.card C)) ≃* C := zmodCyclicMulEquiv hC
  let rot : ZMod (Nat.card C) → G := fun i => (e (Multiplicative.ofAdd i) : C)
  have hrot_mem (i : ZMod (Nat.card C)) : rot i ∈ C := (e (Multiplicative.ofAdd i)).property
  have hrot_add (i j : ZMod (Nat.card C)) : rot (i + j) = rot i * rot j :=
    congrArg Subtype.val (e.map_mul (Multiplicative.ofAdd i) (Multiplicative.ofAdd j))
  have hrot_neg (i : ZMod (Nat.card C)) : rot (-i) = (rot i)⁻¹ :=
    congrArg Subtype.val (e.map_inv (Multiplicative.ofAdd i))
  have hrot_zero : rot 0 = 1 := congrArg Subtype.val e.map_one
  have hw_inv_eq : w⁻¹ = w := (eq_inv_of_mul_eq_one_left hw2).symm
  have hw_mul_rot (i : ZMod (Nat.card C)) : w * rot i = rot (-i) * w := by
    calc w * rot i = (w * rot i * w⁻¹) * w := by rw [hw_inv_eq, mul_assoc, hw2, mul_one]
      _ = (rot i)⁻¹ * w := by rw [hinv (rot i) (hrot_mem i)]
      _ = rot (-i) * w := by rw [hrot_neg]
  have hrot_mul_w (i : ZMod (Nat.card C)) : rot i * w = w * rot (-i) := by
    calc rot i * w = rot (-(-i)) * w := by rw [neg_neg]
      _ = w * rot (-i) := (hw_mul_rot (-i)).symm
  let hom : DihedralGroup (Nat.card C) →* G :=
    { toFun := fun x => match x with
        | DihedralGroup.r i => rot i
        | DihedralGroup.sr i => w * rot i
      map_one' := hrot_zero
      map_mul' := by
        rintro (i | i) (j | j)
        · change rot (i + j) = rot i * rot j
          exact hrot_add i j
        · change w * rot (j - i) = rot i * (w * rot j)
          calc w * rot (j - i) = w * rot (-i + j) := by rw [sub_eq_add_neg, add_comm]
            _ = w * (rot (-i) * rot j) := by rw [hrot_add]
            _ = (w * rot (-i)) * rot j := by rw [mul_assoc]
            _ = (rot i * w) * rot j := by rw [hrot_mul_w]
            _ = rot i * (w * rot j) := by rw [mul_assoc]
        · change w * rot (i + j) = (w * rot i) * rot j
          rw [hrot_add, mul_assoc]
        · change rot (j - i) = (w * rot i) * (w * rot j)
          calc rot (j - i) = rot (-i + j) := by rw [sub_eq_add_neg, add_comm]
            _ = rot (-i) * rot j := hrot_add (-i) j
            _ = (w * w) * (rot (-i) * rot j) := by rw [hw2, one_mul]
            _ = (w * (w * rot (-i))) * rot j := by simp only [mul_assoc]
            _ = (w * (rot i * w)) * rot j := by rw [hrot_mul_w]
            _ = (w * rot i) * (w * rot j) := by simp only [mul_assoc] }
  have hinj : Function.Injective hom := by
    rintro (i | i) (j | j) hij
    · apply congrArg DihedralGroup.r
      change rot i = rot j at hij
      have heq : Multiplicative.ofAdd i = Multiplicative.ofAdd j :=
        e.injective (Subtype.ext hij)
      exact congrArg Multiplicative.toAdd heq
    · exfalso
      apply hw
      change rot i = w * rot j at hij
      have hwrj : w * rot j ∈ C := hij ▸ hrot_mem i
      exact (C.mul_mem_cancel_right (hrot_mem j)).mp hwrj
    · exfalso
      apply hw
      change w * rot i = rot j at hij
      have hwri : w * rot i ∈ C := hij ▸ hrot_mem j
      exact (C.mul_mem_cancel_right (hrot_mem i)).mp hwri
    · apply congrArg DihedralGroup.sr
      change w * rot i = w * rot j at hij
      have heq : Multiplicative.ofAdd i = Multiplicative.ofAdd j :=
        e.injective (Subtype.ext (mul_left_cancel hij))
      exact congrArg Multiplicative.toAdd heq
  have hrange : hom.range = C ⊔ Subgroup.zpowers w := by
    apply le_antisymm
    · rintro x ⟨(i | i), rfl⟩
      · exact Subgroup.mem_sup_left (hrot_mem i)
      · exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
          (Subgroup.mem_sup_left (hrot_mem i))
    · apply sup_le
      · intro c hc
        refine ⟨DihedralGroup.r (Multiplicative.toAdd (e.symm ⟨c, hc⟩)), ?_⟩
        change rot (Multiplicative.toAdd (e.symm ⟨c, hc⟩)) = c
        change ((e (Multiplicative.ofAdd (Multiplicative.toAdd (e.symm ⟨c, hc⟩))) : C) : G) = c
        rw [ofAdd_toAdd, MulEquiv.apply_symm_apply]
      · rw [Subgroup.zpowers_le]
        refine ⟨DihedralGroup.sr 0, ?_⟩
        change w * rot 0 = w
        rw [hrot_zero, mul_one]
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hinj).symm⟩


end SymmetricSubgroupAsymptotics.CyclicInversionDihedralEquivalence
