import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoNonbinary16T1932QuotientSocles

/-! Original16T1932 transitivity uses sixteen selected point words only.
The fixed word (g0*g1)^4 is a nontrivial cubic element. No ambient group or
subgroup enumeration is used. -/
set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoNonbinary16T1932Physical
open PrimitiveAffineDegreeTwoNonbinary16T1932QuotientSocles (Original generators)

def ambient (j : Fin 2) : Original :=
  ⟨generators j,Subgroup.subset_closure (Set.mem_range_self j)⟩
private def pointWords (x : Fin 16) : List (Fin 2) :=
  (#[[],[1,0,1,0],[1,0],[0,0,0,0],[0],[0,1,0],[1,1,1],
    [0,1,0,1,0],[0,0,1,0],[0,0],[1,0,1,1],[1,1],[1,1,0],[0,1,1],[1],[0,0,0]] :
      Array (List (Fin 2)))[x.val]!
private theorem pointWords_checked : ∀ x : Fin 16,
    ((pointWords x).map generators).prod (0 : Fin 16) = x := by decide +kernel

theorem transitive : MulAction.IsPretransitive Original (Fin 16) := by
  apply (MulAction.isPretransitive_iff_base (G := Original) (0 : Fin 16)).mpr
  intro x
  refine ⟨((pointWords x).map ambient).prod,?_⟩
  change (((pointWords x).map ambient).prod : Equiv.Perm (Fin 16)) 0 = x
  simpa [Subgroup.val_list_prod,ambient] using pointWords_checked x

def cubicElement : Original := (ambient 0 * ambient 1)^4

theorem cubic_cube : cubicElement^3=1 := by
  apply Subtype.ext
  change (((generators 0)*(generators 1))^4)^3=1
  decide +kernel

theorem cubic_ne_one : cubicElement ≠ 1 := by
  intro he
  have hx := congrArg (fun g : Original => (g : Equiv.Perm (Fin 16)) 1) he
  have hn : (((generators 0)*(generators 1))^4) (1 : Fin 16) ≠ 1 := by decide +kernel
  exact hn hx

theorem nonbinary : ¬ IsPGroup 2 Original := by
  intro h
  apply cubic_ne_one
  apply (h.powEquiv (by decide : Nat.Coprime 2 3)).injective
  simpa only [IsPGroup.powEquiv_apply,one_pow] using cubic_cube

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoNonbinary16T1932Physical
end
