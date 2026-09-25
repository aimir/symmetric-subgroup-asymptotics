import SymmetricSubgroupAsymptotics.BinaryExceptionalBlocks

/-!
# The proper degree-sixteen carrier correlation

The independent rotation of the literal C4 block is an element of the
full displayed block product, but is absent from the actual carrier.
Thus the reversible chart retains a proper subdirect core.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

private def independentRotationPermutationLiteral0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def independentRotationPermutation (i : Fin 1) : Equiv.Perm (Fin 16) :=
  independentRotationPermutationLiteral0

def independentRotation : Equiv.Perm (Fin 16) :=
  independentRotationPermutation 0

theorem independentRotation_on_cyclic_block : ∀ x,
    independentRotation (block0.embedding x) =
      block0.embedding (block0BaseGenerators 0 x) := by decide +kernel

theorem independentRotation_on_block1 : ∀ x,
    independentRotation (block1.embedding x) = block1.embedding x := by decide +kernel

theorem independentRotation_on_block2 : ∀ x,
    independentRotation (block2.embedding x) = block2.embedding x := by decide +kernel

theorem independentRotation_on_block3 : ∀ x,
    independentRotation (block3.embedding x) = block3.embedding x := by decide +kernel

theorem carrier_nonabelian :
    ∃ x y : Subgroup.closure (Set.range betaGenerators), x*y ≠ y*x := by
  refine ⟨⟨betaGenerators 0, Subgroup.subset_closure (Set.mem_range_self _)⟩,
    ⟨betaGenerators 1, Subgroup.subset_closure (Set.mem_range_self _)⟩, ?_⟩
  intro he
  have hne : betaGenerators 0 * betaGenerators 1 ≠
      betaGenerators 1 * betaGenerators 0 := by decide +kernel
  exact hne (congrArg Subtype.val he)

/-- The independent displayed C4 rotation is absent from the original
literal carrier. Full coordinate projections therefore do not license
replacement by the full displayed product. -/
theorem independentRotation_not_mem : independentRotation ∉
    Subgroup.closure (Set.range betaGenerators) := by
  intro h
  obtain ⟨i,hi⟩ := (betaCertificate.source_mem_iff _).mp h
  have hno : ∀ i, (betaCertificate.cayley.elements i).1 ≠ independentRotation :=
    (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))))
  exact hno i hi

end SymmetricSubgroupAsymptotics.BinaryChart16T1086
