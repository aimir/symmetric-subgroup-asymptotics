import SymmetricSubgroupAsymptotics.Selected1071OriginalKernel

/-! Sixteen selected original words give transitivity directly on original
points. They are read from the selected witness, not an original group census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1071QuotientGraph

private def pointWord (x : Fin 16) : List (Fin 4) :=
  (#[[],[1,3],[2,1,1],[2,3],[1,2,3],[1,2,1,1],[1],[1,1,3],
    [2,3,1,1],[1,1,2,3],[2],[3],[0,2,1],[2,1],[0,3,1],[3,1]] :
      Array (List (Fin 4)))[x.val]!

private theorem pointWord_checked : ∀ x : Fin 16,
    ((pointWord x).map sourceGenerators).prod 0=x := by decide +kernel

private def pointElement (x : Fin 16) : Original := ((pointWord x).map source).prod

private theorem pointElement_zero (x : Fin 16) : pointElement x • (0 : Fin 16)=x := by
  change Original.subtype (((pointWord x).map source).prod) 0=x
  rw [map_list_prod]
  simp only [List.map_map,source,Function.comp_def]
  change ((pointWord x).map sourceGenerators).prod 0=x
  exact pointWord_checked x

instance original_pretransitive : MulAction.IsPretransitive Original (Fin 16) where
  exists_smul_eq x y := by
    refine ⟨pointElement y*(pointElement x)⁻¹,?_⟩
    calc
      _ = pointElement y • ((pointElement x)⁻¹ • x) := mul_smul _ _ _
      _ = pointElement y • ((pointElement x)⁻¹ • (pointElement x • (0 : Fin 16))) :=
        congrArg (fun z => pointElement y • ((pointElement x)⁻¹ • z)) (pointElement_zero x).symm
      _ = y := by rw [inv_smul_smul,pointElement_zero]

end SymmetricSubgroupAsymptotics.Selected1071QuotientGraph
