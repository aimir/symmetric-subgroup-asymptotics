import SymmetricSubgroupAsymptotics.Non2PreE7AffineModel
import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelNumerics

/-!
# Binary primitive affine SAPRIM actions

Let `U = F₂^d ⋊ R`, where `R` is a nontrivial irreducible linear group,
and let `w = 2^d`.  Every nontrivial normal subgroup of `U` contains the
translation subgroup, so every nonbottom literal normal axis is a quotient
of the one comparator `R`.  The comparator acts faithfully on the `w - 1`
nonzero vectors.  The bottom affine fibre has slope exactly `1/2` by the
common-source derived-head theorem.

The source retains the two finite coefficient checks.  They depend only on
the fixed finite action class and are the output expected from the finite
witness exporter; no asymptotic or source-group hypothesis is hidden in
them.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace AffineModel

variable {d : ℕ}

private abbrev BinaryV (d : ℕ) := V 2 d
private abbrev BinaryGLV (d : ℕ) := GLV 2 d

/-- The nonzero vectors of the binary affine space. -/
abbrev NonzeroBinaryV (d : ℕ) := {v : BinaryV d // v ≠ 0}

/-- A linear complement acts on the nonzero vectors. -/
def nonzeroAction (R : Subgroup (BinaryGLV d)) :
    R →* Equiv.Perm (NonzeroBinaryV d) where
  toFun r :=
    { toFun := fun v => ⟨(r : BinaryGLV d) v, by
          intro h
          apply v.2
          exact (r : BinaryGLV d).injective (h.trans (map_zero _).symm)⟩
      invFun := fun v => ⟨((r : BinaryGLV d).symm : BinaryGLV d) v, by
          intro h
          apply v.2
          exact ((r : BinaryGLV d).symm).injective (h.trans (map_zero _).symm)⟩
      left_inv := fun v => Subtype.ext ((r : BinaryGLV d).symm_apply_apply v)
      right_inv := fun v => Subtype.ext ((r : BinaryGLV d).apply_symm_apply v) }
  map_one' := Equiv.ext fun v => Subtype.ext (by
    change (1 : BinaryGLV d) v = v
    rfl)
  map_mul' r s := Equiv.ext fun v => Subtype.ext (by
    change ((r * s : R) : BinaryGLV d) v =
      (r : BinaryGLV d) ((s : BinaryGLV d) v)
    rfl)

theorem nonzeroAction_injective (R : Subgroup (BinaryGLV d)) :
    Function.Injective (nonzeroAction R) := by
  rw [injective_iff_map_eq_one]
  intro r hr
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  by_cases hv : v = 0
  · simp [hv]
  · let x : NonzeroBinaryV d := ⟨v, hv⟩
    have hx := DFunLike.congr_fun hr x
    exact congrArg Subtype.val hx

end AffineModel

namespace Non2UnipotentPrefixFiniteMenu

open AffineModel Equiv SemidirectProduct

/-- An actual retained action identified with a nontrivial binary primitive
affine group.  The coefficient fields are finite checks on this one fixed
action; all dependence on the varying source degree has already been removed.
-/
structure PreE7SaprimBinaryAffineSource
    (w : ℕ) (i : PreE7NonPairActionClass w) : Type where
  d : ℕ
  R : Subgroup (AffineModel.GLV 2 d)
  irreducible : AffineModel.Irreducible R
  length : AffineModel.DerivedLength R
  d_pos : 0 < d
  equiv : preE7NonPairAction w i ≃* AffineModel.Aff R
  nonzeroEquiv : AffineModel.NonzeroBinaryV d ≃ Fin (w - 1)
  width_lower : 8 ≤ w
  width_upper : w < 1024
  width_even : Even w
  main_menu : ∀ b,
    (Nat.card {N : Subgroup (preE7NonPairAction w i) // N.Normal} : ℝ) ≤
      (2 : ℝ) ^ (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
  tail_menu : ∀ b,
    (Nat.card (AffineModel.Aff R ≃* AffineModel.Aff R) : ℝ) ≤
      (2 : ℝ) ^ (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)

namespace PreE7SaprimBinaryAffineSource

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (S : PreE7SaprimBinaryAffineSource w i)

private def comparatorAction :
    S.R →* Equiv.Perm (Fin (w - 1)) :=
  S.nonzeroEquiv.permCongrHom.toMonoidHom.comp (AffineModel.nonzeroAction S.R)

private theorem comparatorAction_injective :
    Function.Injective S.comparatorAction :=
  S.nonzeroEquiv.permCongrHom.injective.comp
    (AffineModel.nonzeroAction_injective S.R)

private theorem affine_epi_le {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (AffineModel.Aff S.R)) : ℝ) ≤
      (Nat.card (AffineModel.Aff S.R ≃* AffineModel.Aff S.R) : ℝ) *
        (2 : ℝ) ^ ((1 / 2 : ℝ) * b) := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h := (AffineModel.target S.irreducible S.length S.d_pos).epi_card_le_prime
    (J := J)
  simpa [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using h

private theorem comparator_window (S : PreE7SaprimBinaryAffineSource w i) :
    preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - ((max 2 (w - 1) : ℕ) : ℝ)) / 8 := by
  have hw8 := S.width_lower
  have hwe : evenWidth w = w := by
    rcases S.width_even with ⟨k, rfl⟩
    unfold evenWidth halfDegree
    omega
  have hmax : max 2 (w - 1) = w - 1 := by omega
  have hsub : (w : ℝ) - ((w - 1 : ℕ) : ℝ) = 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ w)]
    norm_num
  unfold preE7CharacterRho
  rw [hwe, hmax, hsub]
  have hw : (w : ℝ) ≤ 1024 := by exact_mod_cast S.width_upper.le
  norm_num
  linarith

private theorem tail_window (S : PreE7SaprimBinaryAffineSource w i) :
    (1 / 2 : ℝ) ≤ preE7CharacterWindow w := by
  have hw8 : (8 : ℝ) ≤ w := by exact_mod_cast S.width_lower
  have hw1024 : (w : ℝ) ≤ 1024 := by exact_mod_cast S.width_upper.le
  have hhalf : (4 : ℝ) ≤ halfDegree w := by
    obtain ⟨k, hk⟩ := S.width_even
    have hhalfNat : 4 ≤ halfDegree w := by
      have hk8 := S.width_lower
      rw [hk] at hk8
      rw [hk]
      unfold halfDegree
      omega
    exact_mod_cast hhalfNat
  unfold preE7CharacterWindow preE7CharacterRho
  norm_num
  nlinarith

/-- The one-projection normal-comparator model for a binary affine action. -/
def model : PreE7NormalComparatorModel w i where
  G := AffineModel.Aff S.R
  equiv := S.equiv
  index := Unit
  R := S.R
  degree := w - 1
  action := S.comparatorAction
  action_injective := S.comparatorAction_injective
  proj := fun _ => SemidirectProduct.rightHom
  proj_surjective := fun _ => SemidirectProduct.rightHom_surjective
  normal_cover := by
    intro N hN hNb
    letI : N.Normal := hN
    refine ⟨(), ?_⟩
    rw [← SemidirectProduct.range_inl_eq_ker_rightHom]
    exact AffineModel.Vsub_le_normal S.irreducible N hNb
  tailSlope := 1 / 2
  tailConstant := Nat.card (AffineModel.Aff S.R ≃* AffineModel.Aff S.R)
  tailConstant_nonneg := Nat.cast_nonneg _
  tail := fun _ J => S.affine_epi_le J
  comparator_window := comparator_window S
  tail_window := tail_window S

/-- Numerical SAPRIM data for every certified binary primitive affine action. -/
noncomputable def numericalData :
    PreE7SmallAdditiveNumericalData .saprim w i :=
  S.model.numericalData .saprim S.main_menu S.tail_menu

end PreE7SaprimBinaryAffineSource

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
