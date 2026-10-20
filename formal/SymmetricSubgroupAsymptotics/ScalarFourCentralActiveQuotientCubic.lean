import SymmetricSubgroupAsymptotics.ScalarFourCentralActiveQuotientCoordinates

/-! The scalar quotient basis preserves the actual cubic action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
open BinaryQuadraticField
variable {Q T : Type} [Group Q] [Group T] {c d : ℕ}
  (D : ScalarFourCentralTopCoordinates Q T c d)
  (S : Submodule Scalar (Fin d → Scalar))

theorem fieldActive_cubic (n : Q) (hn : D.top n=D.cubic) (k : D.top.ker) :
    (D.fieldActive (MulAut.conjNormal n k)).toAdd=
      omega • (D.fieldActive k).toAdd := by
  change (ScalarFourQuadraticField.tupleEquivalence d
    (D.active (MulAut.conjNormal n k))).toAdd=_
  have he : D.active (MulAut.conjNormal n k)=
      fun j => scalarFourTwist 1 (D.active k j) := by
    funext j
    exact D.cubic_action n hn k j
  rw [he]
  exact ScalarFourQuadraticField.tuple_twist d (D.active k)

theorem quotientActive_cubic (n : Q) (hn : D.top n=D.cubic)
    (k : D.top.ker) (j : Fin (D.activeQuotientRank S)) :
    D.quotientActive S (MulAut.conjNormal n k) j=
      scalarFourTwist 1 (D.quotientActive S k j) := by
  have hcoord (l : D.top.ker) :
      (ScalarFourQuadraticField.tupleEquivalence (D.activeQuotientRank S)
        (D.quotientActive S l)).toAdd=
      D.activeQuotientBasis S (S.mkQ (D.fieldActive l).toAdd) := by
    change ((ScalarFourQuadraticField.tupleEquivalence (D.activeQuotientRank S))
      ((ScalarFourQuadraticField.tupleEquivalence (D.activeQuotientRank S)).symm
        (Multiplicative.ofAdd (D.activeQuotientBasis S
          (S.mkQ (D.fieldActive l).toAdd))))).toAdd=_
    rw [MulEquiv.apply_symm_apply]
    rfl
  have he : D.quotientActive S (MulAut.conjNormal n k)=
      fun i => scalarFourTwist 1 (D.quotientActive S k i) := by
    apply (ScalarFourQuadraticField.tupleEquivalence (D.activeQuotientRank S)).injective
    apply Multiplicative.toAdd.injective
    rw [ScalarFourQuadraticField.tuple_twist,hcoord,hcoord,D.fieldActive_cubic n hn k]
    rw [map_smul,map_smul]
    rfl
  exact congrFun he j

end SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
