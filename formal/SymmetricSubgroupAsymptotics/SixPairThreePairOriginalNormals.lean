import SymmetricSubgroupAsymptotics.SixPairThreePointNormalTop
import SymmetricSubgroupAsymptotics.SixPairThreePairKernelExponent
import SymmetricSubgroupAsymptotics.ProductBlockFrameTransitiveTop
import SymmetricSubgroupAsymptotics.OriginalKernelSmallTopQuotientCard

/-! All nonbinary original normal quotients in the three-top-pairs branch
retain the SAME original coarse kernel and actual three-point top. The
kernel may be noncommutative; only its proved binaryity is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairThreePairOriginalNormals
open OriginalKernelModuleChart

private theorem binary_of_small_residual {G T : Type} [Group G] [Finite G]
    [Group T] [Finite T] (pi : G →* T) (hpi : Function.Surjective pi)
    (hK : IsPGroup 2 pi.ker) (N : Subgroup G) [N.Normal] [(N.map pi).Normal]
    (hs : Nat.card (T ⧸ N.map pi)≤2) : IsPGroup 2 (G ⧸ N) := by
  let R := G ⧸ (pi.ker ⊔ N)
  let f : (G ⧸ N) →* R := base pi N
  have hc : Nat.card R≤2 := (residualTop_card_eq pi hpi N).le.trans hs
  have hr : IsPGroup 2 R := by
    have hp : 0<Nat.card R := Nat.card_pos
    by_cases h1 : Nat.card R=1
    · exact IsPGroup.of_card (n := 0) (by simpa using h1)
    · have h2 : Nat.card R=2 := by omega
      exact IsPGroup.of_card (n := 1) (by simpa only [pow_one] using h2)
  have hk : IsPGroup 2 f.ker :=
    hK.of_surjective (quotientKernelMap pi N) (quotientKernelMap_surjective pi N)
  have hh := (hr.to_subgroup (⊤ : Subgroup R)).comap_of_ker_isPGroup f hk
  have ht : IsPGroup 2 (⊤ : Subgroup (G ⧸ N)) := by
    simpa only [Subgroup.comap_top] using hh
  exact ht.of_equiv Subgroup.topEquiv

/-- No normal denominator with a nonzero coarse-top image can survive as
nonbinary. This covers every original normal axis without a normal census. -/
theorem nonbinary_le_original_kernel
    {U : Subgroup (Equiv.Perm (Fin 12))} [MulAction.IsPretransitive U (Fin 12)]
    (F : BinaryPairFrame U (Fin 6))
    (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))
    (N : Subgroup U) [N.Normal] (hQ : ¬IsPGroup 2 (U ⧸ N)) :
    N≤(SixPairNestedTopFrames.nestedFrame F E).top.ker := by
  let C := SixPairNestedTopFrames.nestedFrame F E
  let T := C.top.range
  let pi : U →* T := C.top.rangeRestrict
  have hpi : Function.Surjective pi := C.top.rangeRestrict_surjective
  have he : pi.ker=C.top.ker := by
    ext u
    change C.top.rangeRestrict u=1 ↔ C.top u=1
    constructor
    · exact fun h => congrArg Subtype.val h
    · exact fun h => Subtype.ext h
  have hk : IsPGroup 2 pi.ker := by
    rw [he]
    exact SixPairThreePairKernelExponent.kernel_binary F E
  letI : MulAction.IsPretransitive T (Fin 3) :=
    ⟨C.top_range_transitive (fun x y => MulAction.exists_smul_eq U x y)⟩
  by_contra hn
  have hm : N.map pi≠⊥ := by
    intro hm
    have hn' := (Subgroup.map_eq_bot_iff (H := N)).mp hm
    exact hn (hn'.trans_eq he)
  letI : (N.map pi).Normal := (inferInstance : N.Normal).map pi hpi
  exact hQ (binary_of_small_residual pi hpi hk N
    (SixPairThreePointNormalTop.quotient_card_le_two T (N.map pi) hm))

end SymmetricSubgroupAsymptotics.SixPairThreePairOriginalNormals
