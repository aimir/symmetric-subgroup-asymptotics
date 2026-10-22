import SymmetricSubgroupAsymptotics.CFSGAffineComponentBoundedOrderNumerics
import SymmetricSubgroupAsymptotics.CFSGAffineComponentPrimeOrderCapacity

/-! All bounded original affine components of local degree at least25,
except32, are paid by the actual full affine order. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.ComponentSource

def of_bounded_localDegree_order_away_thirtyTwo
    {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (hHalf : TraceyAffineHalfInducedModuleInput) (hLog : TraceyAffineInducedModuleInput)
    (hRefined : TraceyRefinedInducedModuleInput) (hPerm : TraceyPermutationGeneratorInput)
    (block : OriginalMinimalBlock (A:=preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hlow : 25 ≤ Nat.card block.Fibre) (hhi : Nat.card block.Fibre < 1024)
    (hne32 : Nat.card block.Fibre ≠ 32) :
    ComponentSource hHalf hLog hRefined hPerm block P := by
  by_cases hprime : (Nat.card block.Fibre).Prime
  · exact of_prime_localDegree_ge_twentyFive_order hHalf hLog hRefined hPerm block P hprime hlow
  letI : Nontrivial block.Fibre := Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply Classical.choice
  obtain ⟨p,d,hp,hd,he,hdiv,hne⟩ := P.exists_prime_dimension_order_divisor block.component_preprimitive
  refine ⟨?_⟩
  have hd2 : 2 ≤ d := by
    by_contra hh
    have hd1 : d=1 := by omega
    apply hprime
    simpa only [he,hd1,pow_one] using hp
  let T := trace hHalf hLog hRefined hPerm block P
  apply of_integer_order_charge hHalf hLog hRefined hPerm block P
    (ArithmeticFunction.cardFactors (fullAffineOrder p d))
  · rw [show tower hHalf hLog hRefined hPerm block P = T.tower from rfl,T.abelianLength_eq]
    exact (actualChiefSeriesAbelianLength_le_cardFactors T.chief).trans
      (CFSGChiefPrimeFactorBudget.cardFactors_mono hne hdiv)
  · rw [he]
    exact fullAffine_component_integer_budget_bounded hp hd2
      (by simpa only [he] using hlow) (by simpa only [he] using hhi)
      (by simpa only [he] using hne32)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.ComponentSource
