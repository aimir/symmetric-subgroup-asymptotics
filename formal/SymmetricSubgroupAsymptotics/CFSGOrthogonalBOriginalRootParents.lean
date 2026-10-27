import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalRootCandidates
import SymmetricSubgroupAsymptotics.CFSGSerreDividedPowerPathComposition
import Mathlib.Data.List.OfFn

/-! Actual source parent paths for the B-transpose family. These identities
are proved in the original integral lattice, with no matrix representation
injectivity or source-span assertion. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalRootParents
open CFSG.Models.Chevalley CFSGOrthogonalBOriginalRootCandidates
open CFSGSerreDividedPowerPathComposition
variable (r : ℕ)

theorem descend_split (i j : Fin r) (hij : i.val < j.val) :
    descend r i j =
      descend r (⟨i.val + 1, by omega⟩ : Fin r) j ++ [i] := by
  have hn : j.val - i.val = (j.val - (i.val + 1)) + 1 := by omega
  unfold descend
  rw [List.ofFn_congr hn, List.ofFn_succ', List.concat_eq_append]
  congr 1
  apply congrArg (fun x : Fin r => [x])
  apply Fin.ext
  simp only [Fin.val_cast, Fin.val_last, Fin.val_mk]
  omega

theorem positive_path_snoc (start : Fin r) (ss : List (Fin r × ℕ))
    (i : Fin r) (k : ℕ) :
    path r false start (ss ++ [(i, k)]) =
      integralOperator (CartanMatrix.B r).transpose false i k (path r false start ss) := by
  simp only [path, Bool.false_eq_true, if_false, one_smul, path_append_step]

theorem positive_double_parent (start : Fin r) (ss : List (Fin r × ℕ)) (i : Fin r) :
    integralOperator (CartanMatrix.B r).transpose false i 1
      (path r false start (ss ++ [(i, 1)])) =
        (2 : ℕ) • path r false start (ss ++ [(i, 2)]) := by
  simp only [path, Bool.false_eq_true, if_false, one_smul]
  exact path_double_step (CartanMatrix.B r).transpose false start ss i

theorem positive_difference_parent (i j : Fin r) (hij : i.val + 1 < j.val) :
    let next : Fin r := ⟨i.val + 1, by omega⟩
    let child : Pair r := ⟨(i, j), by change i.val < j.val; omega⟩
    let parent : Pair r := ⟨(next, j), hij⟩
    integralOperator (CartanMatrix.B r).transpose false i 1 (difference r false parent) =
      difference r false child := by
  dsimp only
  let start : Fin r := ⟨j.val - 1, by omega⟩
  have hs := descend_split r i start (by dsimp [start]; omega)
  simp only [difference]
  change integralOperator _ false i 1 (path r false start _) = path r false start _
  rw [hs]
  simp only [steps, List.map_append, List.map_cons, List.map_nil]
  exact (positive_path_snoc r start _ i 1).symm

theorem positive_short_parent (i : Fin r) (hi : i.val + 1 < r) :
    let next : Fin r := ⟨i.val + 1, hi⟩
    integralOperator (CartanMatrix.B r).transpose false i 1 (short r false next) =
      short r false i := by
  dsimp only
  let last : Fin r := ⟨r - 1, by omega⟩
  have hs := descend_split r i last (by dsimp [last]; omega)
  simp only [short]
  change integralOperator _ false i 1 (path r false last _) = path r false last _
  rw [hs]
  simp only [steps, List.map_append, List.map_cons, List.map_nil]
  exact (positive_path_snoc r last _ i 1).symm

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalRootParents
