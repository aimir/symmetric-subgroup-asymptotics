import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourNonzeroCore

/-! A binary original block kernel forces the actual correlated ternary
core to vanish, independently of the choice of affine translation chart. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]

private def originalBlockKernelProjection :
    block.topMap.ker →* degreeFourQuotientBlockKernel block P where
  toFun k := ⟨QuotientGroup.mk' (E block P) (k : preE7NonPairAction w U),by
    apply MonoidHom.mem_ker.mpr
    change block.topMap.rangeRestrict (k : preE7NonPairAction w U) = 1
    apply Subtype.ext
    exact MonoidHom.mem_ker.mp k.2⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' x y := by apply Subtype.ext; exact map_mul _ _ _

private theorem originalBlockKernelProjection_surjective :
    Function.Surjective (originalBlockKernelProjection block P) := by
  intro q
  obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective (E block P) q.1
  have htop := MonoidHom.mem_ker.mp q.2
  rw [← hg] at htop
  change block.topMap.rangeRestrict g = 1 at htop
  have hk : g ∈ block.topMap.ker := by
    apply MonoidHom.mem_ker.mpr
    exact congrArg Subtype.val htop
  exact ⟨⟨g,hk⟩,Subtype.ext hg⟩

/-- The actual quotient block kernel inherits binary structure from its
original source; this is a surjective image, not subgroup inheritance. -/
theorem degreeFourQuotientBlockKernel_binary_of_original
    (hK : IsPGroup 2 block.topMap.ker) :
    IsPGroup 2 (degreeFourQuotientBlockKernel block P) :=
  hK.of_surjective (originalBlockKernelProjection block P)
    (originalBlockKernelProjection_surjective block P)

/-- Binary original kernel and the actual local card-three coordinates
force the correlated ternary core to be trivial. -/
theorem degreeFourTernaryCore_eq_bot_of_original_blockKernel_binary
    (hr : Nat.card block.Fibre = 4) (hK : IsPGroup 2 block.topMap.ker) :
    degreeFourTernaryCore block P = ⊥ := by
  have hQ := degreeFourQuotientBlockKernel_binary_of_original block P hK
  let inc : degreeFourTernaryCore block P →* degreeFourQuotientBlockKernel block P :=
    Subgroup.inclusion (degreeFourTernaryCore_le_blockKernel block P)
  have hinc : Function.Injective inc := by
    intro x y he
    apply Subtype.ext
    exact congrArg (fun z : degreeFourQuotientBlockKernel block P =>
      (z : DegreeFourComplementQuotient block P)) he
  have hD : IsPGroup 2 (degreeFourTernaryCore block P) := hQ.of_injective inc hinc
  apply le_antisymm
  · intro d hd
    apply Subgroup.mem_bot.mpr
    have he : (⟨d,hd⟩ : degreeFourTernaryCore block P) = 1 := by
      apply degreeFourTernaryCoordinate_joint_injective block P
      funext i
      obtain ⟨k,hk⟩ := hD ⟨d,hd⟩
      have hthree : IsPGroup 3 (degreeFourLocalBinarySign block P).ker :=
        IsPGroup.of_card (n := 1) (by
          simpa only [pow_one] using degreeFourLocalBinarySign_ker_card block P hr)
      apply (hthree.powEquiv ((by decide : Nat.Coprime 3 2).pow_right k)).injective
      have hc := congrArg (degreeFourTernaryCoordinate block P i) hk
      simpa only [IsPGroup.powEquiv_apply,map_pow,map_one,one_pow] using hc
    exact congrArg Subtype.val he
  · exact bot_le

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
end
