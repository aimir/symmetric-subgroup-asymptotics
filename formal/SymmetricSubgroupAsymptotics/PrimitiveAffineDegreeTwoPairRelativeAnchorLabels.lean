import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairRelativeCharacterEnvelope

/-!
# Anchored character labels for pair-relative quotients

This is the counting theorem missing from the old DCHAR/JCHAR framework.
The fixed prefix consists of actual target characters: binary-primary
linear, unrestricted linear, and ordinary irreducible positions.  The
relative tail is a finite label constructed on the anchor preimage (normally
by restricting to a Sylow binary subgroup and applying Frobenius
reciprocity).  Its cardinal estimate is recorded separately, so the theorem
below combines it with the three published complete-source character bounds
and introduces the target automorphism fibre exactly once.

This separation is useful for the pair-top exporter: finite row work chooses
the fixed target characters, while the universal relative-socle theorem
constructs `RelativeLabel` and proves `kernel_eq`.  Neither layer may replace
the latter by a quotient census.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- An actual anchored character tuple on one fixed quotient.  The prefix
characters live on the target.  `RelativeLabel` is the source-dependent
restriction label for all relative positions together; its coefficient is
target-dependent and its exponent is exactly the relative part of the
profile. -/
structure DegreeTwoPairRelativeAnchorLabels
    (Q : Type) [Group Q] [Finite Q]
    (profile : DegreeTwoPairRelativeProfile) : Type 1 where
  binary : Fin profile.binaryPrimary → Q →* ℂˣ
  binary_twoGroup : ∀ i, IsPGroup 2 (binary i).range
  linear : Fin profile.linear → Q →* ℂˣ
  ordinary : Fin profile.ordinary → FiniteIrreducibleRepresentation ℂ Q
  RelativeLabel : (b : ℕ) → Subgroup (Equiv.Perm (Fin b)) → Type
  relativeLabel_finite : ∀ b J, Finite (RelativeLabel b J)
  relativeLabel : ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
    GroupEpimorphism J Q → RelativeLabel b J
  relativeCoefficient : ℝ
  relativeCoefficient_nonneg : 0 ≤ relativeCoefficient
  relative_card_bound : ∀ (b : ℕ)
      (J : Subgroup (Equiv.Perm (Fin b))),
    (Nat.card (RelativeLabel b J) : ℝ) ≤
      relativeCoefficient *
        (2 : ℝ) ^ ((profile.relative : ℝ) *
          Real.logb 2 (38 / 25) * b)
  kernel_eq : ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
      (f g : GroupEpimorphism J Q),
    (∀ i, (binary i).comp f.1 = (binary i).comp g.1) →
    (∀ i, (linear i).comp f.1 = (linear i).comp g.1) →
    (∀ i, Representation.character ((ordinary i).action.comp f.1) =
      Representation.character ((ordinary i).action.comp g.1)) →
    relativeLabel b J f = relativeLabel b J g →
    f.1.ker = g.1.ker

namespace DegreeTwoPairRelativeAnchorLabels

variable {Q : Type} [Group Q] [Finite Q]
  {profile : DegreeTwoPairRelativeProfile}
  (D : DegreeTwoPairRelativeAnchorLabels Q profile)

private theorem product_card_le_two_rpow {n : ℕ}
    (c : Fin n → ℕ) (s : ℝ) (b : ℕ)
    (hc : ∀ i, (c i : ℝ) ≤ (2 : ℝ) ^ (s * b)) :
    ((∏ i, c i : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (((n : ℝ) * s) * b) := by
  push_cast
  calc
    ∏ i, (c i : ℝ) ≤ ∏ _i : Fin n, (2 : ℝ) ^ (s * b) :=
      Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => hc i)
    _ = ((2 : ℝ) ^ (s * b)) ^ n := by simp
    _ = (2 : ℝ) ^ (((n : ℝ) * s) * b) := by
      rw [← Real.rpow_mul_natCast (by norm_num)]
      ring_nf

private theorem four_rpow_mul (a b c d : ℝ) :
    (2 : ℝ) ^ a * (2 : ℝ) ^ b * (2 : ℝ) ^ c *
        (2 : ℝ) ^ d =
      (2 : ℝ) ^ (a + b + c + d) := by
  rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num),
    ← Real.rpow_add (by norm_num)]

/-- The anchored labels give the exact pair-relative quotient envelope.
Binary, linear and ordinary prefix factors are discharged by the named
literature inputs.  Only the relative label uses the special tail bound. -/
noncomputable def toQuotientEnvelope
    (lit : PreE7CharacterLiterature) :
    DegreeTwoPairRelativeQuotientEnvelope Q profile where
  coefficient := D.relativeCoefficient * (Nat.card (Q ≃* Q) : ℝ)
  coefficient_nonneg :=
    mul_nonneg D.relativeCoefficient_nonneg (Nat.cast_nonneg _)
  bound := by
    intro b J
    letI : Invertible (Nat.card J : ℂ) :=
      invertibleOfNonzero (by exact_mod_cast (Nat.card_pos (α := J)).ne')
    let BinaryLabels :=
      ∀ i, linearCharacterLabels (J := J) (D.binary i)
    let LinearLabels :=
      ∀ i, linearCharacterLabels (J := J) (D.linear i)
    let OrdinaryLabels :=
      ∀ i, epimorphismCharacterLabels (J := J) (D.ordinary i).action
    let Label := BinaryLabels × LinearLabels × OrdinaryLabels ×
      D.RelativeLabel b J
    let label : GroupEpimorphism J Q → Label := fun f =>
      (fun i => ⟨(D.binary i).comp f.1, f, rfl⟩,
        fun i => ⟨(D.linear i).comp f.1, f, rfl⟩,
        fun i => ⟨Representation.character
          ((D.ordinary i).action.comp f.1), f, rfl⟩,
        D.relativeLabel b J f)
    letI : Finite (D.RelativeLabel b J) := D.relativeLabel_finite b J
    have hkernel : ∀ f g, label f = label g → f.1.ker = g.1.ker := by
      intro f g h
      have hb := congrArg Prod.fst h
      have hr1 := congrArg Prod.snd h
      have hl := congrArg Prod.fst hr1
      have hr2 := congrArg Prod.snd hr1
      have ho := congrArg Prod.fst hr2
      have hr := congrArg Prod.snd hr2
      apply D.kernel_eq b J f g
      · intro i
        exact congrArg Subtype.val (congrFun hb i)
      · intro i
        exact congrArg Subtype.val (congrFun hl i)
      · intro i
        exact congrArg Subtype.val (congrFun ho i)
      · exact hr
    have hraw := groupEpimorphism_card_le_kernel_labels label hkernel
    have hbin : ((∏ i, Nat.card
        (linearCharacterLabels (J := J) (D.binary i)) : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (((profile.binaryPrimary : ℝ) * (1 / 2)) * b) := by
      apply product_card_le_two_rpow
      intro i
      have h := binaryLinearCharacterSet_card_le
        lit.kovacsPraegerBinary b J
        (linearCharacterLabels (J := J) (D.binary i))
        (linearCharacterLabels_twoGroup _ (D.binary_twoGroup i))
      refine h.trans_eq ?_
      congr 1
      ring
    have hlinear : ((∏ i, Nat.card
        (linearCharacterLabels (J := J) (D.linear i)) : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (((profile.linear : ℝ) *
          (Real.logb 2 3 / 3)) * b) := by
      apply product_card_le_two_rpow
      intro i
      have h1 := linearCharacterSet_card_le_abelianization
        (linearCharacterLabels (J := J) (D.linear i))
      have h2 := lit.kovacsPraeger b J
      calc
        (Nat.card (linearCharacterLabels (J := J) (D.linear i)) : ℝ) ≤
            Nat.card (Abelianization J) := by exact_mod_cast h1
        _ ≤ (3 : ℝ) ^ ((b : ℝ) / 3) := h2
        _ = (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) := by
          rw [show (3 : ℝ) ^ ((b : ℝ) / 3) =
            (2 : ℝ) ^ (Real.logb 2 3 * ((b : ℝ) / 3)) by
              rw [Real.rpow_mul (by norm_num),
                Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]]
          congr 1
          ring
    have hordinary : ((∏ i, Nat.card (epimorphismCharacterLabels
        (J := J) (D.ordinary i).action) : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (((profile.ordinary : ℝ) *
          (Real.logb 2 5 / 3)) * b) := by
      apply product_card_le_two_rpow
      intro i
      have h1 := epimorphismCharacterLabels_card
        (J := J) (D.ordinary i).action
      have h2 := conjClasses_card_le_five_rpow lit.garonziMaroti b J
      calc
        (Nat.card (epimorphismCharacterLabels
            (J := J) (D.ordinary i).action) : ℝ) ≤
            Nat.card (ConjClasses J) := by exact_mod_cast h1
        _ ≤ (5 : ℝ) ^ ((b : ℝ) / 3) := h2
        _ = (2 : ℝ) ^ ((Real.logb 2 5 / 3) * b) := by
          rw [show (5 : ℝ) ^ ((b : ℝ) / 3) =
            (2 : ℝ) ^ (Real.logb 2 5 * ((b : ℝ) / 3)) by
              rw [Real.rpow_mul (by norm_num),
                Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]]
          congr 1
          ring
    have hlabels : (Nat.card Label : ℝ) ≤
        D.relativeCoefficient * (2 : ℝ) ^ (profile.slope * b) := by
      have hbin' : (Nat.card BinaryLabels : ℝ) ≤
          (2 : ℝ) ^ (((profile.binaryPrimary : ℝ) * (1 / 2)) * b) := by
        rw [Nat.card_pi]
        exact hbin
      have hlinear' : (Nat.card LinearLabels : ℝ) ≤
          (2 : ℝ) ^ (((profile.linear : ℝ) *
            (Real.logb 2 3 / 3)) * b) := by
        rw [Nat.card_pi]
        exact hlinear
      have hordinary' : (Nat.card OrdinaryLabels : ℝ) ≤
          (2 : ℝ) ^ (((profile.ordinary : ℝ) *
            (Real.logb 2 5 / 3)) * b) := by
        rw [Nat.card_pi]
        exact hordinary
      simp only [Label, Nat.card_prod]
      push_cast
      calc
        (Nat.card BinaryLabels : ℝ) *
              ((Nat.card LinearLabels : ℝ) *
                ((Nat.card OrdinaryLabels : ℝ) *
                  (Nat.card (D.RelativeLabel b J) : ℝ))) ≤
            (2 : ℝ) ^ (((profile.binaryPrimary : ℝ) * (1 / 2)) * b) *
              ((2 : ℝ) ^ (((profile.linear : ℝ) *
                (Real.logb 2 3 / 3)) * b) *
                ((2 : ℝ) ^ (((profile.ordinary : ℝ) *
                  (Real.logb 2 5 / 3)) * b) *
                  (D.relativeCoefficient *
                    (2 : ℝ) ^ ((profile.relative : ℝ) *
                      Real.logb 2 (38 / 25) * b)))) := by
            apply mul_le_mul hbin'
            · apply mul_le_mul hlinear'
              · exact mul_le_mul hordinary' (D.relative_card_bound b J)
                  (Nat.cast_nonneg _) (Real.rpow_nonneg (by norm_num) _)
              · positivity
              · positivity
            · positivity
            · positivity
        _ = D.relativeCoefficient * (2 : ℝ) ^ (profile.slope * b) := by
          rw [show
            (2 : ℝ) ^ (((profile.binaryPrimary : ℝ) * (1 / 2)) * b) *
                ((2 : ℝ) ^ (((profile.linear : ℝ) *
                  (Real.logb 2 3 / 3)) * b) *
                  ((2 : ℝ) ^ (((profile.ordinary : ℝ) *
                    (Real.logb 2 5 / 3)) * b) *
                    (D.relativeCoefficient *
                      (2 : ℝ) ^ ((profile.relative : ℝ) *
                        Real.logb 2 (38 / 25) * b)))) =
              D.relativeCoefficient *
                ((2 : ℝ) ^ (((profile.binaryPrimary : ℝ) * (1 / 2)) * b) *
                (2 : ℝ) ^ (((profile.linear : ℝ) *
                  (Real.logb 2 3 / 3)) * b) *
                (2 : ℝ) ^ (((profile.ordinary : ℝ) *
                  (Real.logb 2 5 / 3)) * b) *
                (2 : ℝ) ^ ((profile.relative : ℝ) *
                  Real.logb 2 (38 / 25) * b)) by ring]
          rw [four_rpow_mul]
          unfold DegreeTwoPairRelativeProfile.slope
          congr 2
          ring
    have hcast : (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
        (Nat.card Label : ℝ) * (Nat.card (Q ≃* Q) : ℝ) := by
      exact_mod_cast hraw
    calc
      (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
          (Nat.card Label : ℝ) * (Nat.card (Q ≃* Q) : ℝ) := hcast
      _ ≤ (D.relativeCoefficient *
            (2 : ℝ) ^ (profile.slope * b)) *
            (Nat.card (Q ≃* Q) : ℝ) :=
        mul_le_mul_of_nonneg_right hlabels (Nat.cast_nonneg _)
      _ = (D.relativeCoefficient * (Nat.card (Q ≃* Q) : ℝ)) *
            (2 : ℝ) ^ (profile.slope * b) := by ring

end DegreeTwoPairRelativeAnchorLabels

namespace DegreeTwoPairRelativeLiftData

/-- Universal all-original-normal lift from actual anchored character data
on every quotient. -/
noncomputable def ofRelativeAnchorLabels
    {s : ℕ} {p : PreE7PairActionClass s}
    (lit : PreE7CharacterLiterature)
    (profile :
      {N : Subgroup (preE7PairAction s p) // N.Normal} →
        DegreeTwoPairRelativeProfile)
    (capacity : ∀ N,
      (profile N).slope ≤ preE7CharacterWindow (2 * s))
    (data : ∀ N, DegreeTwoPairRelativeAnchorLabels
      (preE7PairAction s p ⧸ N.1) (profile N)) :
    DegreeTwoPairRelativeLiftData s p where
  profile := profile
  capacity := capacity
  envelope N := (data N).toQuotientEnvelope lit

end DegreeTwoPairRelativeLiftData

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
