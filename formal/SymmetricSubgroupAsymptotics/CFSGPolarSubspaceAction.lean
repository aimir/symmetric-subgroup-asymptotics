import SymmetricSubgroupAsymptotics.CFSGPolarSubspaceEquivalence
import Mathlib.GroupTheory.Perm.Basic

/-! Compatible literal actions on singular points and planes lift
coherently to an action on all singular subspaces. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
open CFSGSingularPlaneTriangle
variable {K V A : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Group A]
variable (B : LinearMap.BilinForm K V) (pointHom : A →* Equiv.Perm (Points B))
  (planeHom : A →* Equiv.Perm (Planes B))
  (hinc : ∀a P L,(pointHom a P).val ≤ (planeHom a L).val ↔ P.val ≤ L.val)
  (horth : ∀a P Q,ZeroOn B (pointHom a P).val (pointHom a Q).val ↔ ZeroOn B P.val Q.val)

def subspacePermutation (a : A) : Equiv.Perm (Subspaces B) :=
  (subspaceOrderIso B (pointHom a) (planeHom a) (hinc a) (horth a)).toEquiv

theorem subspacePermutation_incidence (a : A) (W : Subspaces B) (P : Points B) :
    (pointHom a P).val ≤ (subspacePermutation B pointHom planeHom hinc horth a W).val ↔
      P.val ≤ W.val :=
  subspaceOrderIso_point_incidence B (pointHom a) (planeHom a) (hinc a) (horth a) W P

def subspaceAction : A →* Equiv.Perm (Subspaces B) where
  toFun := subspacePermutation B pointHom planeHom hinc horth
  map_one' := by
    apply Equiv.ext
    intro W
    apply subspace_ext B
    intro P
    have h := subspacePermutation_incidence B pointHom planeHom hinc horth 1 W P
    simpa only [map_one,Equiv.Perm.one_apply] using h
  map_mul' := by
    intro a b
    apply Equiv.ext
    intro W
    apply subspace_ext B
    intro P
    obtain ⟨Q,rfl⟩ := (pointHom (a*b)).surjective P
    have hab := subspacePermutation_incidence B pointHom planeHom hinc horth (a*b) W Q
    have ha := subspacePermutation_incidence B pointHom planeHom hinc horth a
      (subspacePermutation B pointHom planeHom hinc horth b W) (pointHom b Q)
    have hb := subspacePermutation_incidence B pointHom planeHom hinc horth b W Q
    have he : pointHom (a*b) Q=pointHom a (pointHom b Q) :=
      congrArg (fun e : Equiv.Perm (Points B)=>e Q) (pointHom.map_mul a b)
    rw [he] at hab ⊢
    exact hab.trans (ha.trans hb).symm

theorem subspaceAction_incidence (a : A) (W : Subspaces B) (P : Points B) :
    (pointHom a P).val ≤ (subspaceAction B pointHom planeHom hinc horth a W).val ↔
      P.val ≤ W.val :=
  subspacePermutation_incidence B pointHom planeHom hinc horth a W P

theorem subspaceAction_preserves_le (a : A) (W Z : Subspaces B) :
    (subspaceAction B pointHom planeHom hinc horth a W).val ≤
      (subspaceAction B pointHom planeHom hinc horth a Z).val ↔ W.val ≤ Z.val :=
  (subspaceOrderIso B (pointHom a) (planeHom a) (hinc a) (horth a)).map_rel_iff

end SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
