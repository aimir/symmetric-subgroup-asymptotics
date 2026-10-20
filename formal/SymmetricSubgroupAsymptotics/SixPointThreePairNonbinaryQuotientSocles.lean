import SymmetricSubgroupAsymptotics.SixPointThreePairCubicQuotientSocles
import SymmetricSubgroupAsymptotics.SixPointThreePairSymmetricRetainedSocles
import SymmetricSubgroupAsymptotics.ThreePointBinaryKernelNormalQuotients

/-! Complete three-pair top geometry: EVERY nonbinary quotient by an
original normal denominator has a normally cyclic socle. Coarse cyclic
and symmetric alternatives follow from the actual three-point action. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SixPointThreePairNonbinaryQuotientSocles

variable {T : Subgroup (Equiv.Perm (Fin 6))} (E : BinaryPairFrame T (Fin 3))

include E in
 theorem quotient [MulAction.IsPretransitive T (Fin 6)]
    (N : Subgroup T) [N.Normal] (hQ : ¬IsPGroup 2 (T ⧸ N)) :
    SocleNormalGeneratorBound (T ⧸ N) 1 := by
  letI : MulAction.IsPretransitive E.top.range (Fin 3) := E.top_pretransitive
  rcases SixPairThreePointNormalTop.cardinal_cases E.top.range with h3 | h6
  · exact SixPointThreePairCubicQuotientSocles.quotient E h3 N
  · have he : E.top.rangeRestrict.ker=E.top.ker := by
      ext t
      change E.top.rangeRestrict t=1 ↔ E.top t=1
      constructor
      · exact fun h => congrArg Subtype.val h
      · exact fun h => Subtype.ext h
    have hk : IsPGroup 2 E.top.rangeRestrict.ker := by
      rw [he]
      exact E.kernel_isPGroup
    have hN : N≤E.top.ker := by
      rw [←he]
      exact ThreePointBinaryKernelNormalQuotients.nonbinary_le_kernel E.top.range
        E.top.rangeRestrict E.top.rangeRestrict_surjective hk N hQ
    have hr : E.top.range=⊤ := Subgroup.eq_top_of_card_eq E.top.range (by
      simpa only [Nat.card_perm,Nat.card_fin] using h6)
    have honto : Function.Surjective E.top := MonoidHom.range_eq_top.mp hr
    exact SixPointThreePairSymmetricRetainedSocles.quotient E honto N hN

end SymmetricSubgroupAsymptotics.SixPointThreePairNonbinaryQuotientSocles
