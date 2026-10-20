import SymmetricSubgroupAsymptotics.StandardGLTwoFiveProjective
import SymmetricSubgroupAsymptotics.PGLTwoFiveRecognition
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Tactic.FinCases

/-! The exceptional isomorphism PGL₂(F₅) ≃ S₅.
The ordinary action on the six projective points is faithful modulo scalar matrices.
Its image has order 120, so the small-index recognition theorem applies.
All field calculations below concern three vectors in a two-dimensional space.
There is no multiplication-table certificate or classification premise. -/

set_option autoImplicit false
noncomputable section
open scoped Classical Matrix
open Equiv Subgroup MulAction
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.PGLTwoFiveIsomorphism

open StandardGLTwoFiveProjective

private instance prime_five : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev VectorFive := Fin 2 → ZMod 5
abbrev PointFive := Projectivization (ZMod 5) VectorFive

/-- The action of actual invertible matrices on their projective lines. -/
def lineAction : LinearFive →* Equiv.Perm PointFive :=
  (MulAction.toPermHom (LinearMap.GeneralLinearGroup (ZMod 5) VectorFive) PointFive).comp
    Matrix.GeneralLinearGroup.toLin.toMonoidHom

private theorem matrix_mulVec_ne_zero (g : LinearFive) (v : VectorFive) (hv : v ≠ 0) :
    (g : Matrix (Fin 2) (Fin 2) (ZMod 5)) *ᵥ v ≠ 0 := by
  change (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv v ≠ 0
  intro hz
  apply hv
  apply (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv.injective
  simpa using hz

private theorem lineAction_mk (g : LinearFive) (v : VectorFive) (hv : v ≠ 0) :
    lineAction g (Projectivization.mk (ZMod 5) v hv) =
      Projectivization.mk (ZMod 5) ((g : Matrix (Fin 2) (Fin 2) (ZMod 5)) *ᵥ v)
        (matrix_mulVec_ne_zero g v hv) := by
  rfl

private theorem scalar_action (u : (ZMod 5)ˣ) :
    lineAction (Matrix.GeneralLinearGroup.scalar (Fin 2) u) = 1 := by
  ext p
  rw [← Projectivization.mk_rep p, lineAction_mk]
  apply (Projectivization.mk_eq_mk_iff (ZMod 5) _ p.rep
    (matrix_mulVec_ne_zero _ _ p.rep_nonzero) p.rep_nonzero).mpr
  refine ⟨u, ?_⟩
  ext i
  fin_cases i <;>
    simp [Units.smul_def, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.GeneralLinearGroup.scalar, Matrix.scalar]

/-- The kernel is exactly the center; three lines already detect scalar matrices. -/
theorem lineAction_ker : lineAction.ker = Subgroup.center LinearFive := by
  ext g
  constructor
  · intro hg
    have hg1 : lineAction g = 1 := MonoidHom.mem_ker.mp hg
    have hfix (v : VectorFive) (hv : v ≠ 0) :
        ∃ u : (ZMod 5)ˣ, u • v = (g : Matrix (Fin 2) (Fin 2) (ZMod 5)) *ᵥ v := by
      apply (Projectivization.mk_eq_mk_iff (ZMod 5) _ v
        (matrix_mulVec_ne_zero g v hv) hv).mp
      rw [← lineAction_mk g v hv, hg1]
      rfl
    have h0 : (![1, 0] : VectorFive) ≠ 0 := by decide
    have h1 : (![0, 1] : VectorFive) ≠ 0 := by decide
    have h2 : (![1, 1] : VectorFive) ≠ 0 := by decide
    obtain ⟨a, ha⟩ := hfix ![1, 0] h0
    obtain ⟨b, hb⟩ := hfix ![0, 1] h1
    obtain ⟨c, hc⟩ := hfix ![1, 1] h2
    have ha0 := congrFun ha 0
    have ha1 := congrFun ha 1
    have hb0 := congrFun hb 0
    have hb1 := congrFun hb 1
    have hc0 := congrFun hc 0
    have hc1 := congrFun hc 1
    simp [Units.smul_def, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at ha0 ha1 hb0 hb1 hc0 hc1
    have hdiag : (g : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 1 = ↑a := by
      calc
        (g : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 1 = ↑c := by
          simpa only [← ha1, zero_add] using hc1.symm
        _ = (g : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0 := by
          simpa only [← hb0, add_zero] using hc0
        _ = ↑a := ha0.symm
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    refine ⟨a, ?_⟩
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.GeneralLinearGroup.scalar, Matrix.scalar] using ha0
    · simpa [Matrix.GeneralLinearGroup.scalar, Matrix.scalar] using hb0
    · simpa [Matrix.GeneralLinearGroup.scalar, Matrix.scalar] using ha1
    · simpa [Matrix.GeneralLinearGroup.scalar, Matrix.scalar] using hdiag.symm
  · intro hg
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg
    obtain ⟨u, rfl⟩ := hg
    exact scalar_action u

theorem card_points : Nat.card PointFive = 6 := by
  rw [Projectivization.card_of_finrank_two (ZMod 5) VectorFive
    (Module.finrank_fin_fun (ZMod 5)), Nat.card_eq_fintype_card, ZMod.card]

def pointsEquiv : PointFive ≃ Fin 6 :=
  Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card]; exact card_points)

def sixAction : LinearFive →* Equiv.Perm (Fin 6) :=
  pointsEquiv.permCongrHom.toMonoidHom.comp lineAction

theorem sixAction_ker : sixAction.ker = Subgroup.center LinearFive := by
  rw [← lineAction_ker]
  ext g
  change pointsEquiv.permCongrHom (lineAction g) = 1 ↔ lineAction g = 1
  constructor
  · intro h
    apply pointsEquiv.permCongrHom.injective
    simpa only [map_one] using h
  · intro h
    rw [h, map_one]

theorem card_projective : Nat.card ProjectiveFive = 120 := by
  have hZ : Nat.card (Subgroup.center LinearFive) = 4 := by
    rw [← Nat.card_congr scalarCenterEquiv.toEquiv]
    exact card_units_five
  have h := (Subgroup.center LinearFive).card_mul_index
  rw [hZ, card_linearFive] at h
  change (Subgroup.center LinearFive).index = 120
  omega

theorem card_range : Nat.card sixAction.range = 120 := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange sixAction).toEquiv]
  rw [sixAction_ker]
  exact card_projective

/-- The precise exceptional isomorphism required by the projective-five facade. -/
def projectiveEquivFive : ProjectiveFive ≃* Equiv.Perm (Fin 5) :=
  (QuotientGroup.quotientMulEquivOfEq sixAction_ker.symm).trans <|
    (QuotientGroup.quotientKerEquivRange sixAction).trans <|
      PGLTwoFiveRecognition.subgroupEquiv sixAction.range card_range

theorem publishedProjectiveIsomorphism : PublishedProjectiveIsomorphism :=
  ⟨projectiveEquivFive⟩

end SymmetricSubgroupAsymptotics.PGLTwoFiveIsomorphism
