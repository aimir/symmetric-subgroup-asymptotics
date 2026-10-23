import SymmetricSubgroupAsymptotics.CFSGHermitianSimilitudeGroup
import Mathlib.Algebra.Group.Subgroup.Finite

/-! The actual multiplier fibre and its uniform finite cardinal bound.
No similitude splitting or norm surjectivity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianSimilitudeGroup
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

theorem multiplier_eq_one_iff (sigma : K ≃+* K) (H : (Matrix I I K)ˣ)
    (i₀ : I) (e : similitudes sigma H) :
    multiplierHom sigma H i₀ e = 1 ↔ e.val ∈ isometries sigma H := by
  constructor
  · intro he v w
    have hh := multiplier_spec sigma H e v w
    change multiplier sigma H e = 1 at he
    rw [he, Units.val_one, one_mul] at hh
    exact hh
  · intro he
    apply Units.ext
    apply multiplier_unique sigma H i₀ e.val
    · exact multiplier_spec sigma H e
    · intro v w
      simpa only [Units.val_one, one_mul] using he v w

def kernelEquivIsometries (sigma : K ≃+* K) (H : (Matrix I I K)ˣ) (i₀ : I) :
    (multiplierHom sigma H i₀).ker ≃* isometries sigma H where
  toFun e := ⟨e.val.val, (multiplier_eq_one_iff sigma H i₀ e.val).mp e.property⟩
  invFun e := ⟨⟨e.val, 1, one_ne_zero, fun v w => by
      simpa only [one_mul] using e.property v w⟩,
    (multiplier_eq_one_iff sigma H i₀ _).mpr e.property⟩
  left_inv e := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv e := by apply Subtype.ext; rfl
  map_mul' e f := by apply Subtype.ext; rfl

theorem similitudes_card_le [Finite K] (sigma : K ≃+* K)
    (hsigma : ∀ x, sigma (sigma x) = x) (eps : K) (H : (Matrix I I K)ˣ)
    (hH : (H : Matrix I I K).map sigma = eps • (H : Matrix I I K).transpose)
    (i₀ : I) :
    Nat.card (similitudes sigma H) ≤ Nat.card (isometries sigma H) * Nat.card (fixedUnits sigma) := by
  let f := fixedMultiplierHom sigma hsigma eps H hH i₀
  have hk : f.ker = (multiplierHom sigma H i₀).ker :=
    MonoidHom.ker_codRestrict _ _ _
  have hkc : Nat.card f.ker = Nat.card (isometries sigma H) := by
    rw [hk]
    exact Nat.card_congr (kernelEquivIsometries sigma H i₀).toEquiv
  have hr : Nat.card f.range ≤ Nat.card (fixedUnits sigma) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  calc
    Nat.card (similitudes sigma H) = Nat.card f.ker * Nat.card f.range := by
      rw [← f.ker.card_mul_index, Subgroup.index_ker]
    _ ≤ Nat.card (isometries sigma H) * Nat.card (fixedUnits sigma) := by
      rw [hkc]
      exact Nat.mul_le_mul_left _ hr

end SymmetricSubgroupAsymptotics.CFSGHermitianSimilitudeGroup
