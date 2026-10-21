import SymmetricSubgroupAsymptotics.CFSGSymplecticCoxeterSingleAction

/-! Signed same-side chain-root matrices. On the positive side these
are the original negative simple roots; on the negative side they are
the negatives of the original positive simple roots. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

def coordinatePoint (r : ℕ) (side : Bool) (i : Fin (r + 1)) : Index (r + 1) :=
  if side then Sum.inr i else Sum.inl i

def signedChainRoot (K : Type) [Field K] (r : ℕ) (side : Bool) (i : Fin r) : Mat K (r + 1) :=
  Matrix.single (coordinatePoint r side i.succ) (coordinatePoint r side i.castSucc) 1 -
    Matrix.single (coordinatePoint r (!side) i.castSucc) (coordinatePoint r (!side) i.succ) 1

theorem coxeterSign_point_of_lt (K : Type) [Field K] (r : ℕ) (side : Bool)
    (i : Fin (r + 1)) (hi : i.val < r) : coxeterSign K r (coordinatePoint r side i) = 1 := by
  have hn : i ≠ Fin.last r := by
    intro h
    have hv := congrArg Fin.val h
    change i.val = r at hv
    omega
  cases side <;> simp only [coordinatePoint, Bool.false_eq_true, coxeterSign, hn, if_false, if_true]

theorem coxeterCycle_point_of_lt (r : ℕ) (side : Bool)
    (i : Fin (r + 1)) (hi : i.val < r) :
    coxeterCycle r (coordinatePoint r side i) =
      coordinatePoint r side (⟨i.val + 1, Nat.succ_lt_succ hi⟩ : Fin (r + 1)) := by
  cases side
  · exact coxeterCycle_inl_of_lt r i.val hi
  · exact coxeterCycle_inr_of_lt r i.val hi

theorem signedChainRoot_false (K : Type) [Field K] (r : ℕ) (i : Fin r) :
    signedChainRoot K r false i = rootMatrix K (r + 1) true i.castSucc := by
  have hlt : i.castSucc.val + 1 < r + 1 := by
    change i.val + 1 < r + 1
    exact Nat.succ_lt_succ i.isLt
  have he : (⟨i.castSucc.val + 1, hlt⟩ : Fin (r + 1)) = i.succ := Fin.ext rfl
  simp only [signedChainRoot, coordinatePoint, Bool.not_false, Bool.false_eq_true,
    if_false, if_true, rootMatrix, negative, positive, hlt, dif_pos,
    Matrix.transpose_sub, Matrix.transpose_single, he]

theorem signedChainRoot_true (K : Type) [Field K] (r : ℕ) (i : Fin r) :
    signedChainRoot K r true i = -rootMatrix K (r + 1) false i.castSucc := by
  have hlt : i.castSucc.val + 1 < r + 1 := by
    change i.val + 1 < r + 1
    exact Nat.succ_lt_succ i.isLt
  have he : (⟨i.castSucc.val + 1, hlt⟩ : Fin (r + 1)) = i.succ := Fin.ext rfl
  simp only [signedChainRoot, coordinatePoint, Bool.not_true, Bool.false_eq_true,
    if_false, if_true, rootMatrix, positive, hlt, dif_pos, he]
  abel

theorem coxeter_signedChainRoot_shift (K : Type) [Field K] (r : ℕ) (side : Bool)
    (i : Fin r) (hi : i.val + 1 < r) :
    ((coxeterWeyl K r).val : Mat K (r + 1)) * signedChainRoot K r side i *
      (↑((coxeterWeyl K r).val⁻¹) : Mat K (r + 1)) =
      signedChainRoot K r side (⟨i.val + 1, hi⟩ : Fin r) := by
  have hi0 : i.castSucc.val < r := i.isLt
  have hi1 : i.succ.val < r := hi
  simp only [signedChainRoot, mul_sub, sub_mul, coxeter_single_conjugation,
    coxeterSign_point_of_lt K r side i.castSucc hi0,
    coxeterSign_point_of_lt K r side i.succ hi1,
    coxeterSign_point_of_lt K r (!side) i.castSucc hi0,
    coxeterSign_point_of_lt K r (!side) i.succ hi1,
    coxeterCycle_point_of_lt r side i.castSucc hi0,
    coxeterCycle_point_of_lt r side i.succ hi1,
    coxeterCycle_point_of_lt r (!side) i.castSucc hi0,
    coxeterCycle_point_of_lt r (!side) i.succ hi1,
    div_one, one_smul]
  rfl

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
