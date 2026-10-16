import SymmetricSubgroupAsymptotics.ProductBlockFrameOriginalBlocks
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockPhysicalFibre
import SymmetricSubgroupAsymptotics.TransitiveStabilizerQuotientKernel
import SymmetricSubgroupAsymptotics.PrimitiveFourPointAffineChoice
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourBinaryBlockKernelZeroCore
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreFourPointSocleSource

/-! A chosen primitive four-by-four physical system with binary original
block kernel gives every actual quotient two socle generators. The only
published parameters are the existing primitive-socle and MN inputs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {U : PreE7NonPairActionClass 16}

/-- All geometry concerns the actual chosen physical chart and kernel. -/
theorem physical_fourByFour_all_quotientSocle_two
    (C : ProductBlockFrame (preE7NonPairAction 16 U) (Fin 4) (Fin 4)) :
    letI : MulAction (preE7NonPairAction 16 U) (Fin 4) := C.topMulAction
    (hc : MulAction.IsPreprimitive
      (originalBlockComponent C.blockMap C.blockMap_equivariant (0 : Fin 4))
      (originalBlockFibre C.blockMap (0 : Fin 4))) →
    (hproper : MulAction.stabilizer (preE7NonPairAction 16 U) (0 : Fin 4) < ⊤) →
    (socle : PublishedPrimitiveSocleDichotomyInput) →
    (hMN : McIverNeumannPermutationGeneratorBound) →
    (hK : IsPGroup 2 C.top.ker) →
    (N : Subgroup (preE7NonPairAction 16 U)) → [N.Normal] →
    SocleNormalGeneratorBound (preE7NonPairAction 16 U ⧸ N) 2 := by
  letI : MulAction (preE7NonPairAction 16 U) (Fin 4) := C.topMulAction
  intro hc hproper socle hMN hK N _
  let base : Fin 16 := C.frame (0,0)
  have hb : C.blockMap base = 0 := by simp [base,ProductBlockFrame.blockMap]
  letI : Nontrivial (originalBlockFibre C.blockMap (C.blockMap base)) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [C.originalFibre_card,Nat.card_fin]; decide)
  have hc' : MulAction.IsPreprimitive
      (originalBlockComponent C.blockMap C.blockMap_equivariant (C.blockMap base))
      (originalBlockFibre C.blockMap (C.blockMap base)) := by
    rw [hb]
    exact hc
  have hproper' : MulAction.stabilizer (preE7NonPairAction 16 U) (C.blockMap base) < ⊤ := by
    rw [hb]
    exact hproper
  let block : OriginalMinimalBlock (A := preE7NonPairAction 16 U) base :=
    C.minimalBlock base hc' hproper'
  have hr : Nat.card block.Fibre = 4 := by
    have he := OriginalMinimalBlock.physicalFibreEquiv C.blockMap C.blockMap_equivariant
      base block rfl
    exact (Nat.card_congr he).trans ((C.originalFibre_card _).trans (Nat.card_fin 4))
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hr]; decide)
  have hs : Nat.card block.Points = 4 := by
    have hp := block.degree_product
    rw [hr,Nat.card_fin] at hp
    omega
  let f : MulActionHom (fun g : preE7NonPairAction 16 U => g) (Fin 16) (Fin 4) := {
    toFun := C.blockMap
    map_smul' := C.blockMap_equivariant }
  have hsurj : Function.Surjective f := by
    intro i
    refine ⟨C.frame (i,0),?_⟩
    change (C.frame.symm (C.frame (i,0))).1=i
    rw [C.frame.symm_apply_apply]
  letI : MulAction.IsPretransitive (preE7NonPairAction 16 U) (Fin 4) :=
    MulAction.IsPretransitive.of_surjective_map (f := f) hsurj inferInstance
  have htop : MulAction.toPermHom (preE7NonPairAction 16 U) (Fin 4) = C.top := by
    apply MonoidHom.ext
    intro g
    apply Equiv.ext
    intro i
    rfl
  have hk : block.topMap.ker = C.top.ker := by
    change (MulAction.toPermHom (preE7NonPairAction 16 U)
      (preE7NonPairAction 16 U ⧸ MulAction.stabilizer (preE7NonPairAction 16 U)
        (C.blockMap base))).ker = C.top.ker
    exact (transitive_stabilizer_quotient_kernel
      (A := preE7NonPairAction 16 U) (C.blockMap base)).trans
      (congrArg MonoidHom.ker htop)
  have hbinary : IsPGroup 2 block.topMap.ker := hk.symm ▸ hK
  let P := primitiveFourPointAffineProfile socle U (by decide) base block hr
  have hD := degreeFourTernaryCore_eq_bot_of_original_blockKernel_binary block P hr hbinary
  exact degreeFourZeroCore_fourPoint_quotientSocle_le_two block P hMN hr hs hD ⟨N,inferInstance⟩

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
end
