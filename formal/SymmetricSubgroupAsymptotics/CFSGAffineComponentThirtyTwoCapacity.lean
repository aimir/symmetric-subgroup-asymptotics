import SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineBinaryFiveAllChiefBound
import SymmetricSubgroupAsymptotics.CFSGAffineComponentOrderCapacity

/-! The original degree32 affine component uses the same actual quotient
trace and the proved all-source binary-five chief bound. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.ComponentSource

def of_localDegree_thirtyTwo_order
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (hHalf : TraceyAffineHalfInducedModuleInput) (hLog : TraceyAffineInducedModuleInput)
    (hRefined : TraceyRefinedInducedModuleInput) (hPerm : TraceyPermutationGeneratorInput)
    (block : OriginalMinimalBlock (A:=preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hr : Nat.card block.Fibre=32) :
    ComponentSource hHalf hLog hRefined hPerm block P := by
  letI : Nontrivial block.Fibre := Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  let C := P.elementaryChart block.component_preprimitive
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  let Q := affineQuotientTrace hHalf hLog hRefined hPerm block P
  let e := P.quotientComplementEquiv (origin block)
  let c := actualChiefSeriesComap e.symm Q.chief
  have hc : actualChiefSeriesAbelianLength c ≤ 4 :=
    P.complementAllChief_abelianLength_le_four_of_degree32 hindex
      block.component_preprimitive C (origin block) hr c
  have hQ : Q.tower.abelianLength ≤ 4 := by
    rw [Q.abelianLength_eq]
    exact (actualChiefSeriesComap_abelianLength e.symm Q.chief).symm.trans_le hc
  have hd : C.d=5 := by
    have he : P.p^C.d=2^5 :=
      (P.degree_eq_prime_pow_finrank C.equiv (origin block)).symm.trans
        (hr.trans (by decide : 32=2^5))
    exact (prime_pow_positive_injective P.p_prime Nat.prime_two C.d_pos (by decide) he).2
  apply of_integer_order_charge hHalf hLog hRefined hPerm block P 9
  · rw [show tower hHalf hLog hRefined hPerm block P =
        (affineTrace hHalf hLog hRefined hPerm block P).tower from rfl,
      affineTrace_abelianLength_eq]
    change C.d+Q.tower.abelianLength ≤ 9
    omega
  · simpa only [hr] using (by decide : 54272*9+38400 ≤ 25575*32)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.ComponentSource
