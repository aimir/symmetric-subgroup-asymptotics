import SymmetricSubgroupAsymptotics.PrimitiveAffineTranslationLayerSource

/-!
# Stop an affine transfer at the literal block top

If the local affine complement image is trivial, the kernel of the compressed
actual-wreath map is exactly the kernel of the original action on blocks.
Consequently the quotient after the translation layer acts faithfully on the
actual set of blocks, rather than on one copy of the nonzero translation set
over every block.  This is the sharp endpoint needed by the zero-complement
small affine cells.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)

variable [Nontrivial block.Fibre]

/-- Membership in the actual translation intersection forces trivial motion
on the literal set of blocks. -/
theorem E_le_topMap_ker : E block P ≤ block.topMap.ker := by
  intro a ha
  apply MonoidHom.mem_ker.mpr
  have hcompressed :
      PermutationalWreathProduct.mapBase (localMap block P)
          (ambientEmbedding block a) = 1 :=
    MonoidHom.mem_ker.mp ha
  have hright := congrArg PermutationalWreathProduct.right hcompressed
  simpa only [PermutationalWreathProduct.mapBase_right,
    PermutationalWreathProduct.one_right] using congrArg Subtype.val hright

/-- If the displayed local complement quotient is trivial, the global
translation intersection is precisely the kernel of the original block-top
action. -/
theorem E_eq_topMap_ker
    (hlocal : ∀ q : LocalQuotient block P, q = 1) :
    E block P = block.topMap.ker := by
  apply le_antisymm (E_le_topMap_ker block P)
  intro a ha
  apply MonoidHom.mem_ker.mpr
  apply PermutationalWreathProduct.ext
  · funext i
    exact hlocal _
  · apply Subtype.ext
    exact MonoidHom.mem_ker.mp ha

/-- The quotient by the actual translation intersection, mapped to the
literal action on blocks. -/
def topQuotientMap :
    (preE7NonPairAction w U ⧸ E block P) →*
      Equiv.Perm block.Points :=
  QuotientGroup.lift (E block P) block.topMap (E_le_topMap_ker block P)

/-- Relabel the literal block set only at the final permutation boundary. -/
def topPointEquiv : block.Points ≃ Fin (Nat.card block.Points) :=
  Finite.equivFin block.Points

/-- The faithful quotient action on the actual blocks. -/
def topQuotientAction :
    (preE7NonPairAction w U ⧸ E block P) →*
      Equiv.Perm (Fin (Nat.card block.Points)) :=
  (topPointEquiv block).permCongrHom.toMonoidHom.comp
    (topQuotientMap block P)

theorem topQuotientMap_injective
    (hlocal : ∀ q : LocalQuotient block P, q = 1) :
    Function.Injective (topQuotientMap block P) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [topQuotientMap, QuotientGroup.ker_lift,
    ← E_eq_topMap_ker block P hlocal]
  exact QuotientGroup.map_mk'_self (E block P)

theorem topQuotientAction_injective
    (hlocal : ∀ q : LocalQuotient block P, q = 1) :
    Function.Injective (topQuotientAction block P) :=
  (topPointEquiv block).permCongrHom.injective.comp
    (topQuotientMap_injective block P hlocal)

/-- A one-layer complete-source envelope ending at the faithful literal
block-top action. -/
noncomputable def topTranslationLayerEnvelope
    (hlocal : ∀ q : LocalQuotient block P, q = 1)
    (H : ElementaryLayerJointCapacityBound
      (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart) :
    RelativeCompleteSourceEnvelope (preE7NonPairAction w U) := by
  letI : Finite (chart block P).V := Finite.of_injective
    (fun v : (chart block P).V =>
      (chart block P).equiv.symm (Multiplicative.ofAdd v))
    (chart block P).equiv.symm.injective
  letI : Finite (TranslationSubmodule block P) :=
    Finite.of_injective (TranslationSubmodule block P).subtype
      (TranslationSubmodule block P).subtype_injective
  letI : Finite (elementaryChart block P).V := by
    change Finite (TranslationSubmodule block P)
    infer_instance
  letI : Finite (elementaryChart block P).quotientRepresentation :=
    inferInstanceAs (Finite (elementaryChart block P).V)
  exact RelativeCompleteSourceEnvelope.elementaryStep
    (p := (elementaryChart block P).p)
    (E block P) (elementaryChart block P) H
    (RelativeCompleteSourceEnvelope.identity
      (preE7NonPairAction w U ⧸ E block P)
      (Nat.card block.Points) (topQuotientAction block P)
      (topQuotientAction_injective block P hlocal))

/-- Construction-facing source obtained by stopping the affine transfer at
the literal block top. -/
noncomputable def topTranslationLayerSource
    (hlocal : ∀ q : LocalQuotient block P, q = 1)
    (H : ElementaryLayerJointCapacityBound
      (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart)
    (hv : 2 ≤ Nat.card block.Points)
    (hm : preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - Nat.card block.Points) / 8 -
        Real.logb 2 (elementaryChart block P).p /
          (elementaryChart block P).p * H.capacity)
    (hD : ∀ b : ℕ, H.coefficient ≤
      (2 : ℝ) ^ (affineComponentWidthCost w +
        8 * (w : ℝ) * Real.logb 2 (b + 1))) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let T := topTranslationLayerEnvelope block P hlocal H
  apply RelativeCompleteSourceEnvelope.toRankTailSourceOrYonedaTopOfMargin
    .acert T
  refine
    { eta_nonneg := ?_
      seedDegree_two_le := ?_
      margin := ?_
      coefficient_bound := ?_ }
  · have hp1 : (1 : ℝ) ≤ (elementaryChart block P).p := by
      exact_mod_cast (elementaryChart block P).p_prime.one_le
    have hlog : 0 ≤ Real.logb 2 (elementaryChart block P).p :=
      Real.logb_nonneg (by norm_num) hp1
    have hp0 : (0 : ℝ) ≤ (elementaryChart block P).p := by positivity
    simpa only [T, topTranslationLayerEnvelope,
      RelativeCompleteSourceEnvelope.elementaryStep,
      RelativeCompleteSourceEnvelope.identity, add_zero] using
      mul_nonneg (div_nonneg hlog hp0) H.capacity_nonneg
  · simpa only [T, topTranslationLayerEnvelope,
      RelativeCompleteSourceEnvelope.elementaryStep,
      RelativeCompleteSourceEnvelope.identity] using hv
  · simpa only [T, topTranslationLayerEnvelope,
      RelativeCompleteSourceEnvelope.elementaryStep,
      RelativeCompleteSourceEnvelope.identity, add_zero] using hm
  · intro b
    simpa only [T, topTranslationLayerEnvelope,
      RelativeCompleteSourceEnvelope.elementaryStep,
      RelativeCompleteSourceEnvelope.identity, mul_one] using hD b

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
