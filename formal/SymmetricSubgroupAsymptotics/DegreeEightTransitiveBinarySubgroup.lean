import SymmetricSubgroupAsymptotics.PrimePowerTransitiveSylow
import SymmetricSubgroupAsymptotics.BinarySylowCoverage
import Mathlib.Tactic.NormNum

/-! An actual transitive binary subgroup inside every transitive degree-eight
source. The subgroup inclusion and original-point action are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem degreeEight_exists_transitive_binary_subgroup
    (T : Subgroup (Equiv.Perm (Fin 8))) (htrans : PermutationSubgroupTransitive T) :
    ∃ P : Subgroup (Equiv.Perm (Fin 8)), P ≤ T ∧ IsPGroup 2 P ∧
      PermutationSubgroupTransitive P := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : MulAction.IsPretransitive T (Fin 8) := ⟨by
    intro x y
    obtain ⟨g, hgT, hg⟩ := htrans x y
    exact ⟨⟨g, hgT⟩, hg⟩⟩
  obtain ⟨Q, hQtrans⟩ := exists_transitive_sylow (G := T) (X := Fin 8) 2 3 (by norm_num)
  let P : Subgroup (Equiv.Perm (Fin 8)) := (Q : Subgroup T).map T.subtype
  refine ⟨P, ?_, Q.isPGroup'.map T.subtype, ?_⟩
  · rintro g ⟨t, _, rfl⟩
    exact t.property
  · intro x y
    obtain ⟨g, hg⟩ := hQtrans.exists_smul_eq x y
    exact ⟨g.val.val, ⟨g.val, g.property, rfl⟩, hg⟩

end SymmetricSubgroupAsymptotics
end
