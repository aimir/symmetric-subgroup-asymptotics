import SymmetricSubgroupAsymptotics.Selected1542TargetQuartetFrame
import SymmetricSubgroupAsymptotics.NaturalA4ScalarFourHead

/-! Literal local A4 generator coordinates and their synchronized cubic
images, bound to the actual twelve-point target generators. -/
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure

def targetSource (j : Fin 3) : literalTarget :=
  ⟨targetGenerators j,Subgroup.subset_closure ⟨j,rfl⟩⟩

theorem targetSource_generates : Subgroup.closure (Set.range targetSource)=⊤ := by
  apply Subgroup.map_injective (f := literalTarget.subtype) Subtype.val_injective
  rw [MonoidHom.map_closure,← Set.range_comp]
  change Subgroup.closure (Set.range targetGenerators)=
    (⊤ : Subgroup literalTarget).map literalTarget.subtype
  rw [← MonoidHom.range_eq_map,Subgroup.range_subtype]
  rfl

def localGenerator (j : Fin 3) (i : Fin 2) : Equiv.Perm (Fin 4) where
  toFun x := ((finProdFinEquiv : Fin 2 × Fin 4 ≃ Fin 8).symm (targetGenerators j ((finProdFinEquiv : Fin 2 × Fin 4 ≃ Fin 8) (i,x)))).2
  invFun x := ((finProdFinEquiv : Fin 2 × Fin 4 ≃ Fin 8).symm ((targetGenerators j)⁻¹ ((finProdFinEquiv : Fin 2 × Fin 4 ≃ Fin 8) (i,x)))).2
  left_inv := by revert j i; decide +kernel
  right_inv := by revert j i; decide +kernel

theorem localGenerator_even : ∀ (j : Fin 3) (i : Fin 2),
    localGenerator j i∈alternatingGroup (Fin 4) := by
  change ∀ (j : Fin 3) (i : Fin 2), Equiv.Perm.sign (localGenerator j i)=1
  decide +kernel

def alternatingGenerator (j : Fin 3) (i : Fin 2) : NaturalA4ScalarFourHead.G :=
  ⟨localGenerator j i,localGenerator_even j i⟩

theorem alternatingGenerator_common : ∀ (j : Fin 3) (i : Fin 2),
    NaturalA4ScalarFourHead.top (alternatingGenerator j i)=
      NaturalA4ScalarFourHead.top (alternatingGenerator j 0) := by decide +kernel

theorem targetLocals_generator (j : Fin 3) :
    targetLocals (targetSource j)=localGenerator j := by
  funext i
  apply Equiv.ext
  intro x
  exact targetLocals_apply (targetSource j) i x

end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
