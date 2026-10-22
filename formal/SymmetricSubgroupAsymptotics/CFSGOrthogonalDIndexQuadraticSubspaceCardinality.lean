import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspaceEquivalence
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Algebra.Module.Submodule.Equiv

/-! Point incidence determines the dimension of an actual Q-zero
subspace over a finite field. The zero subspace is included. -/
set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (Q : QuadraticForm K V)

abbrev PointsInside (W : Subspaces Q) := {P : Points Q // P.val ≤ W.val}

def pointsInsideEquiv (W : Subspaces Q) :
    PointsInside Q W ≃ {L : Submodule K W.val // Module.finrank K L = 1} where
  toFun P := ⟨P.val.val.comap W.val.subtype, by
    have hm : (P.val.val.comap W.val.subtype).map W.val.subtype = P.val.val := by
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr P.property]
    have he := congrArg (fun T : Submodule K V => Module.finrank K T) hm
    change Module.finrank K ((P.val.val.comap W.val.subtype).map W.val.subtype) =
      Module.finrank K P.val.val at he
    exact (Submodule.finrank_map_subtype_eq W.val (P.val.val.comap W.val.subtype)).symm.trans
      (he.trans P.val.property.1)⟩
  invFun L := ⟨⟨L.val.map W.val.subtype,
    (Submodule.finrank_map_subtype_eq W.val L.val).trans L.property, by
      rintro x ⟨x', _, rfl⟩
      exact W.property x'.val x'.property⟩, by
    rintro x ⟨x', _, rfl⟩
    exact x'.property⟩
  left_inv P := by
    apply Subtype.ext
    apply Subtype.ext
    exact (Submodule.map_comap_subtype W.val P.val.val).trans (inf_eq_right.mpr P.property)
  right_inv L := Subtype.ext (Submodule.comap_map_eq_of_injective W.val.subtype_injective L.val)

theorem pointsInside_card_mul [Finite K] (W : Subspaces Q) :
    Nat.card K ^ Module.finrank K W.val = Nat.card (PointsInside Q W) * (Nat.card K - 1) + 1 := by
  let e : W.val ≃ₗ[K] (Fin (Module.finrank K W.val) → K) :=
    LinearEquiv.ofFinrankEq _ _ (by simp)
  letI : Finite W.val := Finite.of_equiv _ e.symm.toEquiv
  have hp : Nat.card (PointsInside Q W) = Nat.card (ℙ K W.val) :=
    (Nat.card_congr (pointsInsideEquiv Q W)).trans
      (Nat.card_congr (Projectivization.equivSubmodule K W.val).symm)
  rw [hp]
  have hc : Nat.card W.val = Nat.card K ^ Module.finrank K W.val := by
    rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_fin]
  exact hc.symm.trans (Projectivization.card' K W.val)

variable (f : Points Q ≃ Points Q) (l : Planes Q ≃ Planes Q)
    (hinc : ∀ P L, (f P).val ≤ (l L).val ↔ P.val ≤ L.val)

def imagePointsEquiv (W : Subspaces Q) : PointsInside Q W ≃ PointsInside Q (imageSubspace Q f l hinc W) where
  toFun P := ⟨f P.val, (point_le_image_iff Q f l hinc W P.val).mpr P.property⟩
  invFun P := ⟨f.symm P.val, (point_le_image_iff Q f l hinc W (f.symm P.val)).mp (by
    simpa only [f.apply_symm_apply] using P.property)⟩
  left_inv P := Subtype.ext (f.symm_apply_apply P.val)
  right_inv P := Subtype.ext (f.apply_symm_apply P.val)

theorem imageSubspace_finrank [Finite K] (W : Subspaces Q) :
    Module.finrank K (imageSubspace Q f l hinc W).val = Module.finrank K W.val := by
  have hc := Nat.card_congr (imagePointsEquiv Q f l hinc W)
  have hp : Nat.card K ^ Module.finrank K (imageSubspace Q f l hinc W).val =
      Nat.card K ^ Module.finrank K W.val := by
    rw [pointsInside_card_mul, pointsInside_card_mul, hc]
  exact Nat.pow_right_injective (Nat.succ_le_iff.mpr (Finite.one_lt_card : 1 < Nat.card K)) hp

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
