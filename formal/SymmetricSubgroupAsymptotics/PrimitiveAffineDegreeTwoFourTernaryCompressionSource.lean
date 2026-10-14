import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopConcreteBranches
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourFiveCharacterIntervalSource

/-!
# The common four-ternary-orbit pair compression source

The eight count-twelve ternary tops do not require eight independent finite
normal-quotient menus.  Their common structural theorem produces, for every
actual degree-twenty-four pair lift, one literal normal subgroup `E`, a
faithful degree-twenty action of the quotient by `E`, and a three-generator
bound for the socle of every quotient below `E`.

This file is the reusable counting adapter for that conclusion.  It retains
the literal interval on the original pair action, applies Zmud only after the
interval is fixed, and uses the already-proved complete character-interval
source.  In particular, no normal subgroup of the degree-twelve top is used
as a surrogate for a normal subgroup of the original pair lift.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

private theorem twelve_lt_twentyFour : 12 < 24 := by decide

/-- The exact output needed from the four-ternary-orbit structural theorem.
The interval belongs to the actual degree-twenty-four action.  Its quotient
acts faithfully on twenty points and every retained quotient has a
three-element normal generating tuple for its whole socle. -/
structure DegreeTwoFourTernaryCompressionData
    (p : PreE7PairActionClass 12) : Type 1 where
  interval : SocleGeneratorCharacterIntervalData
    (preE7NonPairAction 24
      (preE7SmallPairNonPairAction 12 twelve_lt_twentyFour p))
  quotientDegree_eq : interval.quotientDegree = 20
  slots_eq_three : interval.slots = 3

/-- Construction-facing version of the common compression theorem.

The structural proof naturally produces one action of the original pair
lift whose kernel is the averaging subgroup `E1`.  The character interval,
however, asks for an injective action of the quotient by `E1`.  Keeping this
bridge here avoids rebuilding the quotient lift for every one of the eight
finite tops and, more importantly, makes the kernel equality the only
faithfulness statement which the block-parity construction has to prove. -/
structure DegreeTwoFourTernaryCompressionCertificate
    (p : PreE7PairActionClass 12) : Type 1 where
  E : Subgroup
    (preE7NonPairAction 24
      (preE7SmallPairNonPairAction 12 twelve_lt_twentyFour p))
  [E_normal : E.Normal]
  compressedAction :
    preE7NonPairAction 24
      (preE7SmallPairNonPairAction 12 twelve_lt_twentyFour p) →*
        Equiv.Perm (Fin 20)
  compressedAction_ker : compressedAction.ker = E
  quotientSocleGenerators :
    ∀ N : {N : Subgroup
        (preE7NonPairAction 24
          (preE7SmallPairNonPairAction 12 twelve_lt_twentyFour p)) // N.Normal},
      ¬ E ≤ N.1 →
        SocleNormalGeneratorBound
          (preE7NonPairAction 24
            (preE7SmallPairNonPairAction 12 twelve_lt_twentyFour p) ⧸ N.1) 3

attribute [instance]
  DegreeTwoFourTernaryCompressionCertificate.E_normal

namespace DegreeTwoFourTernaryCompressionCertificate

variable {p : PreE7PairActionClass 12}
  (C : DegreeTwoFourTernaryCompressionCertificate p)

/-- The descended degree-twenty action of the exact averaging quotient. -/
def quotientAction :
    (preE7NonPairAction 24
      (preE7SmallPairNonPairAction 12 twelve_lt_twentyFour p) ⧸ C.E) →*
        Equiv.Perm (Fin 20) :=
  QuotientGroup.lift C.E C.compressedAction C.compressedAction_ker.ge

/-- Equality of kernels, rather than a separate quotient calculation,
proves faithfulness of the descended action. -/
theorem quotientAction_injective : Function.Injective C.quotientAction := by
  rw [← MonoidHom.ker_eq_bot_iff, quotientAction,
    QuotientGroup.ker_lift, C.compressedAction_ker,
    QuotientGroup.map_mk'_self]

/-- Install the block-parity action and the whole-socle theorem in the
counting-facing interval record. -/
noncomputable def toCompressionData :
    DegreeTwoFourTernaryCompressionData p where
  interval :=
    { E := C.E
      quotientDegree := 20
      quotientAction := C.quotientAction
      quotientAction_injective := C.quotientAction_injective
      slots := 3
      quotientSocleGenerators := C.quotientSocleGenerators }
  quotientDegree_eq := rfl
  slots_eq_three := rfl

end DegreeTwoFourTernaryCompressionCertificate

namespace DegreeTwoFourTernaryCompressionData

variable {p : PreE7PairActionClass 12}
  (M : DegreeTwoFourTernaryCompressionData p)

/-- Apply the published Zmud theorem to the three normal generators on each
literal retained quotient. -/
noncomputable def completeInterval
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    CompleteCharacterIntervalData
      (preE7NonPairAction 24
        (preE7SmallPairNonPairAction 12 twelve_lt_twentyFour p)) :=
  M.interval.toCompleteCharacterIntervalData hZmud

private theorem logb_two_five_lt_seven_thirds :
    Real.logb 2 5 < (7 : ℝ) / 3 := by
  have hp : (5 : ℝ) ^ (3 : ℕ) < (2 : ℝ) ^ (7 : ℕ) := by
    norm_num
  have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (5 : ℝ) ^ (3 : ℕ)) hp
  simp only [Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hlog
  exact (lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)).2 (by
    simpa only [mul_comm] using hlog)

/-- The generic compression conclusion is a complete QCHAR source at width
twenty four.  The strict degree margin is `20 < 24`; the character tail has
slope `log₂ 5`, since there are exactly three general positions. -/
noncomputable def source
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) :
    PreE7RankTailSourceOrYonedaTopData 24
      (preE7SmallPairNonPairAction 12 twelve_lt_twentyFour p) := by
  let D := M.completeInterval hZmud
  apply boundedCompleteCharacterSource D lit .qchar
  · change preE7CharacterRho * (24 : ℕ) ≤
      ((evenWidth 24 : ℝ) -
        (max 2 M.interval.quotientDegree : ℕ)) / 8
    rw [M.quotientDegree_eq]
    norm_num [preE7CharacterRho, evenWidth, halfDegree]
  · change (M.interval.slots : ℝ) * (Real.logb 2 5 / 3) ≤
      preE7CharacterWindow 24
    rw [M.slots_eq_three]
    norm_num only [Nat.cast_ofNat]
    have hlog := logb_two_five_lt_seven_thirds
    norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree]
    linarith
  · norm_num

/-- Install the shared compression source in one literal ternary catalogue
row.  The top realization is used by the structural constructor of `M`, not
by this numerical adapter. -/
noncomputable def resolvedRow
    {D : DegreeTwoPairTopFiniteInterface 12}
    {expectedProfiles : Finset DegreeTwoPairRelativeProfile}
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) :
    DegreeTwoPairTopResolvedRow D expectedProfiles p :=
  .comparator twelve_lt_twentyFour (M.source hZmud lit)

end DegreeTwoFourTernaryCompressionData

/-- One literal top certificate supplies the same structural compression for
every actual pair lift realizing that top.  This is the per-row datum needed
for each of catalogue rows 37, 77, 117, 168, 210, 214, 242 and 261. -/
structure DegreeTwoTwelveFourTernaryCompressionPackage
    (D : DegreeTwoPairTopFiniteInterface 12) : Type 1 where
  compression : ∀ (p : PreE7PairActionClass 12),
    DegreeTwoPairTopRealization D p →
      DegreeTwoFourTernaryCompressionData p

namespace DegreeTwoTwelveFourTernaryCompressionPackage

variable {D : DegreeTwoPairTopFiniteInterface 12}
  (F : DegreeTwoTwelveFourTernaryCompressionPackage D)

/-- Dispatch one checked top package to an arbitrary actual realization of
that top. -/
noncomputable def catalogueResolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    {expectedProfiles : Finset DegreeTwoPairRelativeProfile}
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) :
    DegreeTwoPairTopResolvedRow D expectedProfiles p :=
  (F.compression p R).resolvedRow hZmud lit

end DegreeTwoTwelveFourTernaryCompressionPackage

/-- Assemble a count-twelve catalogue with the common four-ternary
compression on its ternary rows.  This is the direct replacement for the
older degree-eight finite-QCHAR row argument: the source here remains on the
actual original pair lift and uses the faithful degree-twenty quotient
action. -/
noncomputable def degreeTwoTwelveResolution_of_relative_and_fourTernary
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (T : DegreeTwoTwelvePairTopFiniteCatalogue)
    (relative : ∀ (j : Fin 301) (p : PreE7PairActionClass 12),
      DegreeTwoPairTopRealization (T.row j).finite p →
      (T.row j).branch ≠ .ternary →
      DegreeTwoPairTopRelativeResolvedData (T.row j).finite
        (T.row j).expectedProfiles p)
    (ternary : ∀ (j : Fin 301) (p : PreE7PairActionClass 12),
      DegreeTwoPairTopRealization (T.row j).finite p →
      (T.row j).branch = .ternary →
      DegreeTwoFourTernaryCompressionData p) :
    DegreeTwoTwelvePairTopCatalogueResolution T := by
  intro j p realization
  by_cases h : (T.row j).branch = .ternary
  · exact (ternary j p realization h).resolvedRow hZmud lit
  · exact (relative j p realization h).toResolvedRow

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
