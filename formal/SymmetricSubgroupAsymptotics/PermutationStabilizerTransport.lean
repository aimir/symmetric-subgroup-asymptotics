import SymmetricSubgroupAsymptotics.BinaryConjugacyTransport
import SymmetricSubgroupAsymptotics.OrbitProfileAssembly

/-! Point stabilizers under actual permutation relabelling and conjugation.
The stabilizer chart commutes with the ambient chart on every element. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.PermutationStabilizerTransport

variable {X Y : Type} (S : Subgroup (Equiv.Perm X)) (T : Subgroup (Equiv.Perm Y))
  (points : X ≃ Y) (g : Equiv.Perm Y)
  (matched : MulAut.conj g • relabelSubgroup points S = T)

def groupEquiv : S ≃* T :=
  (points.permCongrHom.subgroupMap S).trans (actionConjugacyEquiv g matched)

def pointEquiv : X ≃ Y := points.trans g

theorem groupEquiv_action (s : S) (x : X) :
    (groupEquiv S T points g matched s).1 (pointEquiv points g x) =
      pointEquiv points g (s.1 x) := by
  simp [groupEquiv, pointEquiv, actionConjugacyEquiv, Equiv.permCongr_apply]

def stabilizerEquiv (y : Y) :
    MulAction.stabilizer S ((pointEquiv points g).symm y) ≃*
      MulAction.stabilizer T y where
  toFun s := ⟨groupEquiv S T points g matched s.1, by
    have hs : s.1.1 ((pointEquiv points g).symm y) = (pointEquiv points g).symm y := s.2
    have ha := groupEquiv_action S T points g matched s.1 ((pointEquiv points g).symm y)
    simpa only [Equiv.apply_symm_apply, hs] using ha⟩
  invFun t := ⟨(groupEquiv S T points g matched).symm t.1, by
    apply (pointEquiv points g).injective
    have ha := groupEquiv_action S T points g matched
      ((groupEquiv S T points g matched).symm t.1) ((pointEquiv points g).symm y)
    rw [MulEquiv.apply_symm_apply, Equiv.apply_symm_apply] at ha
    have ht : t.1.1 y = y := t.2
    exact ha.symm.trans (ht.trans (Equiv.apply_symm_apply _ _).symm)⟩
  left_inv s := by
    apply Subtype.ext
    exact (groupEquiv S T points g matched).symm_apply_apply s.1
  right_inv t := by
    apply Subtype.ext
    exact (groupEquiv S T points g matched).apply_symm_apply t.1
  map_mul' s t := by
    apply Subtype.ext
    exact (groupEquiv S T points g matched).map_mul s.1 t.1

theorem stabilizerEquiv_commutes (y : Y)
    (s : MulAction.stabilizer S ((pointEquiv points g).symm y)) :
    groupEquiv S T points g matched s.1 =
      (stabilizerEquiv S T points g matched y s).1 := rfl

end SymmetricSubgroupAsymptotics.PermutationStabilizerTransport

end
