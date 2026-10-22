import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMiddleSupport

/-! The literal middle embedding preserves the actual upper subgroup.
This provides the honest inductive construction of regular unipotents,
without a full-unitary recognition or derived-membership premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryUpperArrays
open CFSGTwistedAUpperUnipotent

theorem naturalMiddleHom_upper (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalUnipotent s q) :
    naturalToSpecialLinear (q.Extension 2) (s + 2)
      (naturalMiddleHom (q.Extension 2) s g.val) ∈
        CFSGUpperUnitriangular.upperUnitriangular (q.Extension 2) (s + 3) := by
  constructor
  · intro i j hij
    obtain ⟨x, rfl⟩ := (splitEquiv s).surjective i
    obtain ⟨y, rfl⟩ := (splitEquiv s).surjective j
    change ((naturalFixedMiddleHom q s ⟨g.val, g.property.2⟩).val.val :
      Mat (q.Extension 2) (s + 2)) (splitEquiv s x) (splitEquiv s y) = 0
    rw [naturalFixedMiddleHom_apply]
    rcases x with u | (i | u) <;> rcases y with v | (j | v)
    all_goals try cases u
    all_goals try cases v
    all_goals try { rfl }
    all_goals try {
      apply g.property.1.1
      change j.val < i.val
      change j.val + 1 < i.val + 1 at hij
      omega }
    all_goals change _ < _ at hij
    all_goals simp only [id_eq, splitEquiv, Equiv.coe_fn_mk, splitIndex,
      Fin.lt_def, Fin.val_zero, Fin.val_last, Fin.val_mk] at hij
    all_goals try have hi := i.isLt
    all_goals try have hj := j.isLt
    all_goals omega
  · intro i
    obtain ⟨x, rfl⟩ := (splitEquiv s).surjective i
    change ((naturalFixedMiddleHom q s ⟨g.val, g.property.2⟩).val.val :
      Mat (q.Extension 2) (s + 2)) (splitEquiv s x) (splitEquiv s x) = 1
    rw [naturalFixedMiddleHom_apply]
    rcases x with u | (i | u)
    · rfl
    · exact g.property.1.2 i
    · rfl

def middleUnipotentHom (q : CFSG.PrimePower) (s : ℕ) :
    naturalUnipotent s q →* naturalUnipotent (s + 2) q where
  toFun g := ⟨naturalMiddleHom (q.Extension 2) s g.val,
    naturalMiddleHom_upper q s g, naturalMiddleHom_fixed q s ⟨g.val, g.property.2⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g.val h.val)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
