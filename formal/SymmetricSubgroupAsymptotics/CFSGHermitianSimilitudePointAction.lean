import SymmetricSubgroupAsymptotics.CFSGHermitianSimilitudeCardinality
import SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
import Mathlib.GroupTheory.Index

/-! Literal Hermitian similitudes act on the original singular lines.
Every nonzero scalar lies in the kernel; its full unit count cancels
against any proved linear-similitude cardinal bound. No geometric
reconstruction or surjective multiplier hypothesis is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianSimilitudeGroup
open CFSGTwistedAUnitaryParameters CFSGHermitianOrthogonalSpan
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

local instance [Finite K] : Finite (LinearGroup (K := K) (I := I)) :=
  Finite.of_injective (fun L : LinearGroup (K := K) (I := I) =>
    (L : (I → K) → I → K)) DFunLike.coe_injective

theorem singular_map_iff (sigma : K ≃+* K) (H : (Matrix I I K)ˣ)
    (g : similitudes sigma H) (P : Submodule K (I → K)) :
    (∀ x ∈ P.map g.val.toLinearMap, hermitianPair sigma H x x = 0) ↔
      ∀ x ∈ P, hermitianPair sigma H x x = 0 := by
  constructor
  · intro h x hx
    have he := h (g.val x) ⟨x,hx,rfl⟩
    rw [multiplier_spec] at he
    exact (mul_eq_zero.mp he).resolve_left (Units.ne_zero _)
  · rintro h x ⟨v,hv,rfl⟩
    change hermitianPair sigma (H : Matrix I I K) (g.val v) (g.val v) = 0
    rw [multiplier_spec sigma H g v v, h v hv, mul_zero]

def singularPointEquiv (sigma : K ≃+* K) (H : (Matrix I I K)ˣ)
    (g : similitudes sigma H) : Equiv.Perm (SingularPoint sigma (H : Matrix I I K)) :=
  Equiv.subtypeEquiv (Submodule.orderIsoMapComap g.val).toEquiv (fun P => by
    change (Module.finrank K P = 1 ∧ ∀ x ∈ P, hermitianPair sigma H x x = 0) ↔
      (Module.finrank K (P.map g.val.toLinearMap) = 1 ∧
        ∀ x ∈ P.map g.val.toLinearMap, hermitianPair sigma H x x = 0)
    rw [g.val.finrank_map_eq, singular_map_iff sigma H g P])

def singularPointHom (sigma : K ≃+* K) (H : (Matrix I I K)ˣ) :
    similitudes sigma H →* Equiv.Perm (SingularPoint sigma (H : Matrix I I K)) where
  toFun := singularPointEquiv sigma H
  map_one' := by
    apply Equiv.ext
    intro P
    apply Subtype.ext
    change P.val.map (LinearEquiv.refl K (I → K)).toLinearMap = P.val
    exact Submodule.map_id P.val
  map_mul' g h := by
    apply Equiv.ext
    intro P
    apply Subtype.ext
    change P.val.map (g.val * h.val).toLinearMap =
      (P.val.map h.val.toLinearMap).map g.val.toLinearMap
    rw [← Submodule.map_comp]
    rfl

theorem singularPointHom_val (sigma : K ≃+* K) (H : (Matrix I I K)ˣ)
    (g : similitudes sigma H) (P : SingularPoint sigma (H : Matrix I I K)) :
    (singularPointHom sigma H g P).val = P.val.map g.val.toLinearMap := rfl

def scalarSimilitude (sigma : K ≃+* K) (H : (Matrix I I K)ˣ) (c : Kˣ) :
    similitudes sigma H :=
  ⟨LinearEquiv.smulOfUnit c, sigma (c : K) * (c : K),
    mul_ne_zero ((map_ne_zero sigma).mpr (Units.ne_zero c)) (Units.ne_zero c),
    fun v w => by
      change hermitianPair sigma H ((c : K) • v) ((c : K) • w) = _
      rw [hermitianPair_smul, mul_assoc]⟩

theorem scalarSimilitude_mem_kernel (sigma : K ≃+* K) (H : (Matrix I I K)ˣ) (c : Kˣ) :
    scalarSimilitude sigma H c ∈ (singularPointHom sigma H).ker := by
  apply MonoidHom.mem_ker.mpr
  apply Equiv.ext
  intro P
  apply Subtype.ext
  rw [singularPointHom_val]
  apply le_antisymm
  · rintro v ⟨u,hu,rfl⟩
    exact P.val.smul_mem (c : K) hu
  · intro v hv
    refine ⟨((c⁻¹ : Kˣ) : K) • v,P.val.smul_mem _ hv,?_⟩
    change (c : K) • (((c⁻¹ : Kˣ) : K) • v) = v
    rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

def scalarToPointKernel (sigma : K ≃+* K) (H : (Matrix I I K)ˣ) (c : Kˣ) :
    (singularPointHom sigma H).ker :=
  ⟨scalarSimilitude sigma H c,scalarSimilitude_mem_kernel sigma H c⟩

theorem scalarToPointKernel_injective [Nonempty I] (sigma : K ≃+* K)
    (H : (Matrix I I K)ˣ) : Function.Injective (scalarToPointKernel sigma H) := by
  intro c d he
  have hh := congrArg (fun g : (singularPointHom sigma H).ker => g.val.val (fun _ => 1)) he
  apply Units.ext
  have hv := congrFun hh (Classical.choice (inferInstance : Nonempty I))
  change (c : K) * 1 = (d : K) * 1 at hv
  simpa only [mul_one] using hv

theorem singularPointImage_card_le_of_scalar_bound [Finite K] [Nonempty I]
    (sigma : K ≃+* K) (H : (Matrix I I K)ˣ) (B : ℕ)
    (hbound : Nat.card (similitudes sigma H) ≤ B * Nat.card Kˣ) :
    Nat.card (singularPointHom sigma H).range ≤ B := by
  have hk : Nat.card Kˣ ≤ Nat.card (singularPointHom sigma H).ker :=
    Nat.card_le_card_of_injective (scalarToPointKernel sigma H)
      (scalarToPointKernel_injective sigma H)
  have he := (singularPointHom sigma H).ker.card_mul_index
  rw [Subgroup.index_ker] at he
  have hb : Nat.card Kˣ * Nat.card (singularPointHom sigma H).range ≤ Nat.card Kˣ * B := by
    calc
      _ ≤ Nat.card (singularPointHom sigma H).ker * Nat.card (singularPointHom sigma H).range :=
        Nat.mul_le_mul_right _ hk
      _ = Nat.card (similitudes sigma H) := he
      _ ≤ Nat.card Kˣ * B := hbound.trans_eq (Nat.mul_comm _ _)
  exact Nat.le_of_mul_le_mul_left hb (Nat.card_pos (α := Kˣ))

end SymmetricSubgroupAsymptotics.CFSGHermitianSimilitudeGroup
