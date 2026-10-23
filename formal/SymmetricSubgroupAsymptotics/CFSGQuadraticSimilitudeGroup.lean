import SymmetricSubgroupAsymptotics.CFSGQuadraticSimilitudeGeometry
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.Finite

/-! Multiplier pairs form the genuine similitude group of any quadratic
form. Its multiplier-one kernel is the actual isometry group. On finite
singular-point actions the scalar kernel cancels the multiplier budget,
without requiring multiplier surjectivity or an isometry identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticSimilitudeGroup
open CFSGOrthogonalDIndexQuadraticSubspacePoints
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

local instance [Finite V] : Finite (V ≃ₗ[K] V) :=
  Finite.of_injective (fun L : V ≃ₗ[K] V => (L : V → V)) DFunLike.coe_injective

def isometries (Q : QuadraticForm K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {L | ∀ v, Q (L v) = Q v}
  one_mem' := fun _ => rfl
  mul_mem' hL hM v := (hL _).trans (hM v)
  inv_mem' {L} hL v := by
    have h := hL (L.symm v)
    rw [L.apply_symm_apply] at h
    exact h.symm

def similitudes (Q : QuadraticForm K V) : Subgroup ((V ≃ₗ[K] V) × Kˣ) where
  carrier := {g | ∀ v, Q (g.1 v) = (g.2 : K) * Q v}
  one_mem' := by
    intro v
    exact (one_mul _).symm
  mul_mem' {g h} hg hh := by
    intro v
    change Q (g.1 (h.1 v)) = ((g.2 * h.2 : Kˣ) : K) * Q v
    rw [hg, hh, Units.val_mul, mul_assoc]
  inv_mem' {g} hg := by
    intro v
    have h := hg (g.1.symm v)
    rw [g.1.apply_symm_apply] at h
    change Q (g.1.symm v) = ((g.2⁻¹ : Kˣ) : K) * Q v
    rw [Units.val_inv_eq_inv_val, h, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero g.2), one_mul]

def multiplier (Q : QuadraticForm K V) : similitudes Q →* Kˣ :=
  (MonoidHom.snd (V ≃ₗ[K] V) Kˣ).comp (similitudes Q).subtype

def kernelEquivIsometries (Q : QuadraticForm K V) : (multiplier Q).ker ≃ isometries Q where
  toFun g := ⟨g.val.val.1, by
    intro v
    have he := g.val.property v
    have hc : g.val.val.2 = 1 := g.property
    rw [hc, Units.val_one, one_mul] at he
    exact he⟩
  invFun L := ⟨⟨(L.val, 1), fun v => by
    simpa only [Units.val_one, one_mul] using L.property v⟩, rfl⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact g.property.symm
  right_inv L := by
    apply Subtype.ext
    rfl

theorem similitudes_card_le [Finite K] [Finite V] (Q : QuadraticForm K V) :
    Nat.card (similitudes Q) ≤ Nat.card (isometries Q) * Nat.card Kˣ := by
  have hk : Nat.card (multiplier Q).ker = Nat.card (isometries Q) :=
    Nat.card_congr (kernelEquivIsometries Q)
  have hr : Nat.card (multiplier Q).range ≤ Nat.card Kˣ :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  calc
    Nat.card (similitudes Q) = Nat.card (multiplier Q).ker * Nat.card (multiplier Q).range := by
      rw [← (multiplier Q).ker.card_mul_index, Subgroup.index_ker]
    _ ≤ Nat.card (isometries Q) * Nat.card Kˣ := by
      rw [hk]
      exact Nat.mul_le_mul_left _ hr

variable [FiniteDimensional K V]

def pointHom (Q : QuadraticForm K V) : similitudes Q →* Equiv.Perm (Points Q) where
  toFun g := CFSGQuadraticSimilitudeGeometry.pointEquiv Q g.val.1 (g.val.2 : K)
    (Units.ne_zero g.val.2) g.property
  map_one' := by
    apply Equiv.ext
    intro P
    apply Subtype.ext
    change P.val.map (LinearEquiv.refl K V).toLinearMap = P.val
    exact Submodule.map_id P.val
  map_mul' g h := by
    apply Equiv.ext
    intro P
    apply Subtype.ext
    change P.val.map (g.val.1 * h.val.1).toLinearMap =
      (P.val.map h.val.1.toLinearMap).map g.val.1.toLinearMap
    rw [← Submodule.map_comp]
    rfl

theorem pointHom_val (Q : QuadraticForm K V) (g : similitudes Q) (P : Points Q) :
    (pointHom Q g P).val = P.val.map g.val.1.toLinearMap := rfl

def scalarElement (Q : QuadraticForm K V) (c : Kˣ) : similitudes Q :=
  ⟨(LinearEquiv.smulOfUnit c, c ^ 2), fun v => by
    change Q ((c : K) • v) = ((c ^ 2 : Kˣ) : K) * Q v
    rw [Q.map_smul]
    simp only [pow_two, Units.val_mul, smul_eq_mul]⟩

theorem scalar_mem_kernel (Q : QuadraticForm K V) (c : Kˣ) : scalarElement Q c ∈ (pointHom Q).ker := by
  apply MonoidHom.mem_ker.mpr
  apply Equiv.ext
  intro P
  apply Subtype.ext
  rw [pointHom_val]
  apply le_antisymm
  · rintro v ⟨u, hu, rfl⟩
    exact P.val.smul_mem (c : K) hu
  · intro v hv
    refine ⟨((c⁻¹ : Kˣ) : K) • v, P.val.smul_mem _ hv, ?_⟩
    change (c : K) • (((c⁻¹ : Kˣ) : K) • v) = v
    rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

def scalarToKernel (Q : QuadraticForm K V) (c : Kˣ) : (pointHom Q).ker :=
  ⟨scalarElement Q c, scalar_mem_kernel Q c⟩

theorem scalarToKernel_injective [Nontrivial V] (Q : QuadraticForm K V) :
    Function.Injective (scalarToKernel Q) := by
  intro c d he
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h := congrArg (fun g : (pointHom Q).ker => g.val.val.1 v) he
  apply Units.ext
  exact smul_left_injective K hv h

theorem pointImage_card_le_isometries [Finite K] [Finite V] [Nontrivial V]
    (Q : QuadraticForm K V) : Nat.card (pointHom Q).range ≤ Nat.card (isometries Q) := by
  have hk : Nat.card Kˣ ≤ Nat.card (pointHom Q).ker :=
    Nat.card_le_card_of_injective (scalarToKernel Q) (scalarToKernel_injective Q)
  have he := (pointHom Q).ker.card_mul_index
  rw [Subgroup.index_ker] at he
  have hbound : Nat.card Kˣ * Nat.card (pointHom Q).range ≤
      Nat.card Kˣ * Nat.card (isometries Q) := by
    calc
      Nat.card Kˣ * Nat.card (pointHom Q).range ≤
          Nat.card (pointHom Q).ker * Nat.card (pointHom Q).range := Nat.mul_le_mul_right _ hk
      _ = Nat.card (similitudes Q) := he
      _ ≤ Nat.card Kˣ * Nat.card (isometries Q) :=
        (similitudes_card_le Q).trans_eq (Nat.mul_comm _ _)
  exact Nat.le_of_mul_le_mul_left hbound (Nat.card_pos (α := Kˣ))

end SymmetricSubgroupAsymptotics.CFSGQuadraticSimilitudeGroup
