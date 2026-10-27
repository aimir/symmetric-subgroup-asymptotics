import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalRootCandidates
import SymmetricSubgroupAsymptotics.CFSGSerreChevalleyInvolution

/-! Genuine Chevalley exchange of the SAME original B paths. Both the
negative-path sign and the sum-root outer minus sign are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalChevalleyPaths
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreDividedPowerPaths
open CFSGSerreChevalleyInvolution CFSGOrthogonalBOriginalRootCandidates
variable (r : ℕ)

theorem map_operator (neg : Bool) (i : Fin r) (k : ℕ) (x : Source r) :
    integralMap (CartanMatrix.B r).transpose (integralOperator (CartanMatrix.B r).transpose neg i k x) =
      integralOperator (CartanMatrix.B r).transpose (!neg) i k
        (integralMap (CartanMatrix.B r).transpose x) := by
  apply Subtype.ext
  exact rationalMap_dividedPower (CartanMatrix.B r).transpose neg i k x.val

private theorem map_steps (neg : Bool) (ss : List (Fin r × ℕ)) (x : Source r) :
    integralMap (CartanMatrix.B r).transpose (applySteps (CartanMatrix.B r).transpose neg ss x) =
      applySteps (CartanMatrix.B r).transpose (!neg) ss
        (integralMap (CartanMatrix.B r).transpose x) := by
  induction ss generalizing x with
  | nil => rfl
  | cons s ss ih => simp only [applySteps, ih, map_operator]

private theorem map_pathVector (neg : Bool) (start : Fin r) (ss : List (Fin r × ℕ)) :
    integralMap (CartanMatrix.B r).transpose (pathVector (CartanMatrix.B r).transpose neg start ss) =
      pathVector (CartanMatrix.B r).transpose (!neg) start ss := by
  unfold pathVector
  rw [map_steps]
  congr 1
  apply Subtype.ext
  change rationalMap (CartanMatrix.B r).transpose
    (generator (CartanMatrix.B r).transpose (if neg then .F start else .E start)) =
      generator (CartanMatrix.B r).transpose (if !neg then .F start else .E start)
  cases neg
  · exact rationalMap_E (CartanMatrix.B r).transpose start
  · exact rationalMap_F (CartanMatrix.B r).transpose start

theorem map_path_positive (start : Fin r) (ss : List (Fin r × ℕ)) :
    integralMap (CartanMatrix.B r).transpose (path r false start ss) =
      (-1 : ℤ) ^ (ss.map Prod.snd).sum • path r true start ss := by
  simp only [path, Bool.false_eq_true, if_false, if_true, one_smul, map_pathVector]
  rcases neg_one_pow_eq_or ℤ (ss.map Prod.snd).sum with h | h <;> simp [h]

theorem map_path_negative (start : Fin r) (ss : List (Fin r × ℕ)) :
    integralMap (CartanMatrix.B r).transpose (path r true start ss) =
      (-1 : ℤ) ^ (ss.map Prod.snd).sum • path r false start ss := by
  simp only [path, Bool.false_eq_true, if_false, if_true, one_smul, map_smul,
    map_pathVector, Bool.not_true]

theorem map_root_swap (sgn : Bool) (j : RootIndex r) : ∃ z : ℤ,
    integralMap (CartanMatrix.B r).transpose (root r sgn j) = z • root r (!sgn) j := by
  cases sgn
  · rcases j with ij | (i | ij)
    · exact ⟨_, map_path_positive r _ _⟩
    · exact ⟨_, map_path_positive r _ _⟩
    · let last : Fin r := ⟨r - 1, by have h := ij.val.2.isLt; omega⟩
      let previous : Fin r := ⟨r - 2, by have h := ij.property; have hj := ij.val.2.isLt; omega⟩
      let ss := steps r (descend r ij.val.1 previous) 1 ++ [(last, 2)] ++
        steps r (descend r ij.val.2 last) 1
      refine ⟨(-1 : ℤ) ^ (ss.map Prod.snd).sum, ?_⟩
      change integralMap _ ((-1 : ℤ) • path r false previous ss) =
        ((-1 : ℤ) ^ (ss.map Prod.snd).sum) • ((-1 : ℤ) • path r true previous ss)
      rw [map_smul, map_path_positive]
      simp only [smul_smul]
      congr 1
      ring
  · rcases j with ij | (i | ij)
    · exact ⟨_, map_path_negative r _ _⟩
    · exact ⟨_, map_path_negative r _ _⟩
    · let last : Fin r := ⟨r - 1, by have h := ij.val.2.isLt; omega⟩
      let previous : Fin r := ⟨r - 2, by have h := ij.property; have hj := ij.val.2.isLt; omega⟩
      let ss := steps r (descend r ij.val.1 previous) 1 ++ [(last, 2)] ++
        steps r (descend r ij.val.2 last) 1
      refine ⟨(-1 : ℤ) ^ (ss.map Prod.snd).sum, ?_⟩
      change integralMap _ ((-1 : ℤ) • path r true previous ss) =
        ((-1 : ℤ) ^ (ss.map Prod.snd).sum) • ((-1 : ℤ) • path r false previous ss)
      rw [map_smul, map_path_negative]
      simp only [smul_smul]
      congr 1
      ring

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalChevalleyPaths
