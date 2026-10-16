import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction025Generators
import Mathlib.GroupTheory.GroupAction.Transitive

/-! The selected action25 is transitive and nonbinary on its original
physical12points, from selected point words and one actual cubic element. -/
set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoSixPairAction025LightPhysical

abbrev Original := Subgroup.closure
  (Set.range PrimitiveAffineDegreeTwoSixPairAction025Generators.generators)

abbrev generators := PrimitiveAffineDegreeTwoSixPairAction025Generators.generators

def ambient (j : Fin 5) : Original :=
  ⟨generators j,Subgroup.subset_closure (Set.mem_range_self j)⟩

private def pointWords (x : Fin 12) : List (Fin 5) :=
  (#[[],[0],[3,2,2],[3,2,2,0],[3,2],[3,2,0],[4],[4,0],[2,2],[2,2,0],[2],[2,0]] : Array (List (Fin 5)))[x.val]!
private theorem pointWords_checked : ∀ x : Fin 12,
    ((pointWords x).map generators).prod (0 : Fin 12) = x := by decide +kernel

theorem transitive : MulAction.IsPretransitive Original (Fin 12) := by
  apply (MulAction.isPretransitive_iff_base (G := Original) (0 : Fin 12)).mpr
  intro x
  refine ⟨((pointWords x).map ambient).prod,?_⟩
  change (((pointWords x).map ambient).prod : Equiv.Perm (Fin 12)) 0 = x
  simpa [Subgroup.val_list_prod,ambient] using pointWords_checked x

def cubicElement : Original := ambient 2

theorem cubic_cube : cubicElement ^ 3 = 1 := by
  apply Subtype.ext
  change (generators 2)^3=1
  decide +kernel

theorem cubic_ne_one : cubicElement ≠ 1 := by
  intro he
  have hx := congrArg (fun g : Original => (g : Equiv.Perm (Fin 12)) 0) he
  have hn : generators 2 (0 : Fin 12) ≠ 0 := by decide +kernel
  exact hn hx

theorem nonbinary : ¬ IsPGroup 2 Original := by
  intro h
  apply cubic_ne_one
  apply (h.powEquiv (by decide : Nat.Coprime 2 3)).injective
  simpa only [IsPGroup.powEquiv_apply,one_pow] using cubic_cube

end PrimitiveAffineDegreeTwoSixPairAction025LightPhysical
end SymmetricSubgroupAsymptotics
end
