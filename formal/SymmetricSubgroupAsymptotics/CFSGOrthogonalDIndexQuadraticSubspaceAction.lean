import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspaceEquivalence
import Mathlib.GroupTheory.Perm.Basic

/-! Compatible original actions on Q-singular points and planes extend
coherently to every original Q-singular subspace. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
variable {K V A : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Group A]
variable (Q : QuadraticForm K V) (pointHom : A →* Equiv.Perm (Points Q))
    (planeHom : A →* Equiv.Perm (Planes Q))
    (hinc : ∀ a P L, (pointHom a P).val ≤ (planeHom a L).val ↔ P.val ≤ L.val)

def subspacePermutation (a : A) : Equiv.Perm (Subspaces Q) :=
  (subspaceOrderIso Q (pointHom a) (planeHom a) (hinc a)).toEquiv

theorem subspacePermutation_incidence (a : A) (W : Subspaces Q) (P : Points Q) :
    (pointHom a P).val ≤ (subspacePermutation Q pointHom planeHom hinc a W).val ↔
      P.val ≤ W.val := subspaceOrderIso_point_incidence Q (pointHom a) (planeHom a) (hinc a) W P

def subspaceAction : A →* Equiv.Perm (Subspaces Q) where
  toFun := subspacePermutation Q pointHom planeHom hinc
  map_one' := by
    apply Equiv.ext
    intro W
    apply subspace_ext Q
    intro P
    have h := subspacePermutation_incidence Q pointHom planeHom hinc 1 W P
    simpa only [map_one, Equiv.Perm.one_apply] using h
  map_mul' := by
    intro a b
    apply Equiv.ext
    intro W
    apply subspace_ext Q
    intro P
    obtain ⟨R, rfl⟩ := (pointHom (a * b)).surjective P
    have hab := subspacePermutation_incidence Q pointHom planeHom hinc (a * b) W R
    have ha := subspacePermutation_incidence Q pointHom planeHom hinc a
      (subspacePermutation Q pointHom planeHom hinc b W) (pointHom b R)
    have hb := subspacePermutation_incidence Q pointHom planeHom hinc b W R
    have he : pointHom (a * b) R = pointHom a (pointHom b R) :=
      congrArg (fun e : Equiv.Perm (Points Q) => e R) (pointHom.map_mul a b)
    rw [he] at hab ⊢
    exact hab.trans (ha.trans hb).symm

theorem subspaceAction_incidence (a : A) (W : Subspaces Q) (P : Points Q) :
    (pointHom a P).val ≤ (subspaceAction Q pointHom planeHom hinc a W).val ↔ P.val ≤ W.val :=
  subspacePermutation_incidence Q pointHom planeHom hinc a W P

theorem subspaceAction_preserves_le (a : A) (W Z : Subspaces Q) :
    (subspaceAction Q pointHom planeHom hinc a W).val ≤
      (subspaceAction Q pointHom planeHom hinc a Z).val ↔ W.val ≤ Z.val :=
  (subspaceOrderIso Q (pointHom a) (planeHom a) (hinc a)).map_rel_iff

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
