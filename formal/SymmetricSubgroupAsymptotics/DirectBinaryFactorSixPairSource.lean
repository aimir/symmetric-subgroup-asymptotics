import SymmetricSubgroupAsymptotics.DirectBinaryFactorCharacterAxes
import SymmetricSubgroupAsymptotics.CharacterAxisEquivTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairGeneralSourceAssembly

/-! Actual images of H × C2 inherit the all-original-normal mixed source.
The source is constructed from the concrete model map and proved normal
socle bounds of H; no final-source premise is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.DirectBinaryFactorSixPairSource
open Non2UnipotentPrefixFiniteMenu
variable {H : Type} [Group H] [Finite H]

/-- The kernel is taken after the actual original denominator N, so every
axis remains an axis of the SAME original target quotient. -/
def axis_of_surjective
    (hH : ∀ (M : Subgroup H) [M.Normal], SocleNormalGeneratorBound (H ⧸ M) 1)
    {Q : Type} [Group Q] (rho : H × DirectBinaryFactorCharacterAxes.Bit →* Q)
    (hrho : Function.Surjective rho) (N : Subgroup Q) [N.Normal] :
    PreE7B6CharacterAxisData (Q ⧸ N) :=
  let phi := (QuotientGroup.mk' N).comp rho
  (DirectBinaryFactorCharacterAxes.axis hH phi.ker).mapEquiv
    (QuotientGroup.quotientKerEquivOfSurjective phi
      ((QuotientGroup.mk'_surjective N).comp hrho))

/-- Complete exact representative-facing width12 source. -/
def source
    (hH : ∀ (M : Subgroup H) [M.Normal], SocleNormalGeneratorBound (H ⧸ M) 1)
    (hZmud : ZmudFaithfulCharacterTupleInput) (p : PreE7PairActionClass 6)
    (rho : H × DirectBinaryFactorCharacterAxes.Bit →* preE7PairAction 6 p)
    (hrho : Function.Surjective rho) :
    PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) := by
  let axes : PreE7B6CharacterOnlyQuotientData (preE7PairAction 6 p) :=
    PreE7B6CharacterOnlyQuotientData.ofAxes hZmud (fun N => by
      letI : N.val.Normal := N.property
      exact axis_of_surjective hH rho hrho N.val)
  exact .inl (.b6 (axes.toB6ActionCertificate (preE7PairFrame 6 p)))

end SymmetricSubgroupAsymptotics.DirectBinaryFactorSixPairSource
