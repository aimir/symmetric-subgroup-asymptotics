import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeBlockNativeSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockBinaryForwardTerminal

/-!
# The honest sign-isotype split in the four-block local-S3 cell

The binary four-block residual is not uniformly a repeated-marker family.
Its literal signed permutation module has four coordinate characters.  The
actual transitive block top permutes their equality classes transitively, so
the number of distinct character classes is `1`, `2`, or `4`.

This file records that retained structural datum and the only routes which
are valid after it is known.

* one character is the diagonal branch; it may use the central-sign owner,
  or an exact positive forward row proved from a diagonal marker splice;
* two characters use the audited `S3TWO` complete-source envelope;
* four characters are singleton weight spaces.  A nonzero invariant ternary
  kernel is then the full faithful irreducible module, so the audited
  faithful-irreducible `S3EXC` envelope applies;
* a non-diagonal branch may instead be discharged by an already proved
  direct residual source, or retained in a general forward continuation.

In particular there is no constructor asserting a marker embedding for an
arbitrary signed action.  The old universal pointed-marker boundary is not
used here.

The held mathematical sources for the three structural branches are
`non2_central_sign_small_s3_forward_working.md`,
`non2_four_s3_two_sign_forward_working.md`, and the faithful-irreducible
part of `non2_small_partial_s3_exceptions_working.md`, together with their
independent audits.  The remaining concrete theorem is the literal bridge
from `degreeNineLinearBlockKernel` and the actual four coordinate signs to
one of the constructors below.
-/

set_option autoImplicit false
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
  [Nontrivial block.Fibre]

/-- The literal equality partition of the four coordinate sign characters.

`Sign` is the finite type of characters which actually occur, rather than a
freely chosen list of abstract binary characters.  Surjectivity prevents
unused labels.  `uniform_fibre` is the consequence of transitivity of the
actual block top.  The final disjunction is the finite conclusion of that
orbit argument; keeping it in this record makes the precise remaining
group-theoretic bridge visible without pretending that the pair chart alone
already contains coordinate-character data. -/
structure DegreeThreeFourBlockSignedIsotypeProfile : Type 2 where
  Sign : Type
  [finiteSign : Finite Sign]
  coordinateSign : Fin 4 → Sign
  coordinateSign_surjective : Function.Surjective coordinateSign
  multiplicity : ℕ
  multiplicity_pos : 0 < multiplicity
  uniform_fibre : ∀ χ : Sign,
    Nat.card {i : Fin 4 // coordinateSign i = χ} = multiplicity
  isotype_count_cases :
    Nat.card Sign = 1 ∨ Nat.card Sign = 2 ∨ Nat.card Sign = 4

attribute [instance]
  DegreeThreeFourBlockSignedIsotypeProfile.finiteSign

namespace DegreeThreeFourBlockSignedIsotypeProfile

def isotypeCount (C : DegreeThreeFourBlockSignedIsotypeProfile) : ℕ :=
  Nat.card C.Sign

theorem cases (C : DegreeThreeFourBlockSignedIsotypeProfile) :
    C.isotypeCount = 1 ∨ C.isotypeCount = 2 ∨ C.isotypeCount = 4 :=
  C.isotype_count_cases

/-- The singleton-isotype case has four different literal coordinate
characters. -/
theorem coordinateSign_injective_of_isotypeCount_eq_four
    (C : DegreeThreeFourBlockSignedIsotypeProfile)
    (hfour : C.isotypeCount = 4) :
    Function.Injective C.coordinateSign := by
  exact ((Nat.bijective_iff_surjective_and_card C.coordinateSign).mpr
    ⟨C.coordinateSign_surjective, by
      simpa only [Nat.card_fin, isotypeCount] using hfour.symm⟩).injective

end DegreeThreeFourBlockSignedIsotypeProfile

namespace BinaryPairFrame

variable {X : Type} {G : Subgroup (Equiv.Perm X)}

/-- The actual coordinate character of a pair kernel.  It is deliberately
kept as the literal function on `F.top.ker`; equality of these functions is
the sign-isotype relation used by the historical proof. -/
def fourCoordinateSignFunction
    (F : BinaryPairFrame G (Fin 4)) (i : Fin 4) : F.top.ker → ZMod 2 :=
  fun k ↦ F.bits k i

/-- The finite type of coordinate characters which actually occur. -/
def FourCoordinateSign (F : BinaryPairFrame G (Fin 4)) : Type :=
  Set.range (fourCoordinateSignFunction F)

/-- Each literal pair coordinate retains its actual character. -/
def fourCoordinateSign
    (F : BinaryPairFrame G (Fin 4)) (i : Fin 4) : FourCoordinateSign F :=
  ⟨fourCoordinateSignFunction F i, i, rfl⟩

theorem fourCoordinateSign_surjective
    (F : BinaryPairFrame G (Fin 4)) :
    Function.Surjective (fourCoordinateSign F) := by
  rintro ⟨χ, i, rfl⟩
  exact ⟨i, rfl⟩

noncomputable instance fourCoordinateSign_finite
    (F : BinaryPairFrame G (Fin 4)) : Finite (FourCoordinateSign F) :=
  Finite.of_surjective (fourCoordinateSign F)
    (fourCoordinateSign_surjective F)

private theorem fourCoordinateSignFunction_top
    (F : BinaryPairFrame G (Fin 4)) (u : G) (i : Fin 4) :
    fourCoordinateSignFunction F (F.top u i) =
      fun k ↦ fourCoordinateSignFunction F i (MulAut.conjNormal u⁻¹ k) := by
  funext k
  simpa only [fourCoordinateSignFunction, map_inv, inv_inv] using
    (F.bits_conjNormal u⁻¹ k i).symm

private theorem fourCoordinateSign_top_imp
    (F : BinaryPairFrame G (Fin 4)) (u : G) (i j : Fin 4)
    (h : fourCoordinateSign F i = fourCoordinateSign F j) :
    fourCoordinateSign F (F.top u i) =
      fourCoordinateSign F (F.top u j) := by
  apply Subtype.ext
  change fourCoordinateSignFunction F (F.top u i) =
    fourCoordinateSignFunction F (F.top u j)
  rw [fourCoordinateSignFunction_top F,
    fourCoordinateSignFunction_top F]
  exact congrArg
    (fun f : F.top.ker → ZMod 2 ↦
      fun k ↦ f (MulAut.conjNormal u⁻¹ k))
    (congrArg Subtype.val h)

/-- Conjugation by an actual source element preserves, and reflects, equality
of coordinate characters. -/
theorem fourCoordinateSign_top_eq_iff
    (F : BinaryPairFrame G (Fin 4)) (u : G) (i j : Fin 4) :
    fourCoordinateSign F (F.top u i) =
        fourCoordinateSign F (F.top u j) ↔
      fourCoordinateSign F i = fourCoordinateSign F j := by
  constructor
  · intro h
    have h' := fourCoordinateSign_top_imp F u⁻¹
      (F.top u i) (F.top u j) h
    simpa using h'
  · intro h
    exact fourCoordinateSign_top_imp F u i j h

/-- The actual top permutation gives an equivalence between the two literal
coordinate-character fibres. -/
def fourCoordinateSignFiberEquiv
    (F : BinaryPairFrame G (Fin 4)) (u : G) (i : Fin 4) :
    {j : Fin 4 // fourCoordinateSign F j = fourCoordinateSign F i} ≃
      {j : Fin 4 // fourCoordinateSign F j =
        fourCoordinateSign F (F.top u i)} where
  toFun j := ⟨F.top u j,
    (fourCoordinateSign_top_eq_iff F u j.1 i).2 j.2⟩
  invFun j := ⟨(F.top u)⁻¹ j,
    (fourCoordinateSign_top_eq_iff F u ((F.top u)⁻¹ j.1) i).1 (by
      simpa using j.2)⟩
  left_inv j := by
    apply Subtype.ext
    exact (F.top u).symm_apply_apply j
  right_inv j := by
    apply Subtype.ext
    exact (F.top u).apply_symm_apply j

/-- Transitivity of the literal source action makes all actual
coordinate-character classes equicardinal. -/
theorem fourCoordinateSign_fibre_card_eq
    (F : BinaryPairFrame G (Fin 4))
    (htrans : MulAction.IsPretransitive G X)
    (χ ψ : FourCoordinateSign F) :
    Nat.card {i : Fin 4 // fourCoordinateSign F i = χ} =
      Nat.card {i : Fin 4 // fourCoordinateSign F i = ψ} := by
  obtain ⟨i, rfl⟩ := fourCoordinateSign_surjective F χ
  obtain ⟨j, rfl⟩ := fourCoordinateSign_surjective F ψ
  letI : MulAction.IsPretransitive G X := htrans
  letI : MulAction.IsPretransitive F.top.range (Fin 4) := F.top_pretransitive
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq F.top.range i j
  obtain ⟨u, rfl⟩ := F.top.rangeRestrict_surjective t
  have htop : F.top u i = j := by simpa using ht
  simpa only [htop] using Nat.card_congr (fourCoordinateSignFiberEquiv F u i)

attribute [local instance] Fintype.ofFinite

/-- A transitive equality partition of four coordinates has one, two, or
four classes.  This is the complete numerical sign-isotype split; in
particular the apparent three-character case cannot occur. -/
theorem fourCoordinateSign_count_cases
    (F : BinaryPairFrame G (Fin 4))
    (htrans : MulAction.IsPretransitive G X) :
    Nat.card (FourCoordinateSign F) = 1 ∨
      Nat.card (FourCoordinateSign F) = 2 ∨
      Nat.card (FourCoordinateSign F) = 4 := by
  let m := Nat.card {i : Fin 4 //
    fourCoordinateSign F i = fourCoordinateSign F 0}
  have hm : 0 < m := Nat.card_pos_iff.mpr
    ⟨⟨⟨0, rfl⟩⟩, inferInstance⟩
  have hproduct :
      Nat.card (FourCoordinateSign F) * m = 4 := by
    calc
      Nat.card (FourCoordinateSign F) * m =
          ∑ _χ : FourCoordinateSign F, m := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          Fintype.card_eq_nat_card, Nat.cast_id]
      _ = ∑ χ : FourCoordinateSign F,
          Nat.card {i : Fin 4 // fourCoordinateSign F i = χ} := by
        apply Finset.sum_congr rfl
        intro χ _hχ
        exact (fourCoordinateSign_fibre_card_eq F htrans χ
          (fourCoordinateSign F 0)).symm
      _ = Nat.card (Σ χ : FourCoordinateSign F,
          {i : Fin 4 // fourCoordinateSign F i = χ}) := Nat.card_sigma.symm
      _ = Nat.card (Fin 4) :=
        Nat.card_congr (Equiv.sigmaFiberEquiv (fourCoordinateSign F))
      _ = 4 := Nat.card_fin 4
  have hqpos : 0 < Nat.card (FourCoordinateSign F) :=
    Nat.card_pos_iff.mpr
      ⟨⟨fourCoordinateSign F 0⟩, inferInstance⟩
  have hqle : Nat.card (FourCoordinateSign F) ≤ 4 := by
    calc
      Nat.card (FourCoordinateSign F) =
          Nat.card (FourCoordinateSign F) * 1 := by omega
      _ ≤ Nat.card (FourCoordinateSign F) * m :=
        Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr hm)
      _ = 4 := hproduct
  interval_cases hq : Nat.card (FourCoordinateSign F) <;> omega

/-- The one-isotype branch is exactly the diagonal binary kernel: every
literal kernel element has the same flip bit in all four coordinates. -/
theorem fourCoordinateSign_count_eq_one_iff_bits_constant
    (F : BinaryPairFrame G (Fin 4)) :
    Nat.card (FourCoordinateSign F) = 1 ↔
      ∀ (k : F.top.ker) (i j : Fin 4), F.bits k i = F.bits k j := by
  constructor
  · intro hone
    letI : Subsingleton (FourCoordinateSign F) :=
      (Nat.card_eq_one_iff_unique.mp hone).1
    intro k i j
    exact congrFun (congrArg Subtype.val
      (Subsingleton.elim (fourCoordinateSign F i)
        (fourCoordinateSign F j))) k
  · intro hconstant
    apply Nat.card_eq_one_iff_unique.mpr
    refine ⟨?_, ⟨fourCoordinateSign F 0⟩⟩
    constructor
    intro χ ψ
    obtain ⟨i, rfl⟩ := fourCoordinateSign_surjective F χ
    obtain ⟨j, rfl⟩ := fourCoordinateSign_surjective F ψ
    apply Subtype.ext
    funext k
    exact hconstant k i j

/-- Construct the retained isotype profile directly from the literal pair
frame.  The character labels, surjectivity, common multiplicity and the
`1/2/4` split are all recovered from the actual action. -/
noncomputable def fourCoordinateSignedIsotypeProfile
    (F : BinaryPairFrame G (Fin 4))
    (htrans : MulAction.IsPretransitive G X) :
    DegreeThreeFourBlockSignedIsotypeProfile where
  Sign := FourCoordinateSign F
  coordinateSign := fourCoordinateSign F
  coordinateSign_surjective := fourCoordinateSign_surjective F
  multiplicity := Nat.card {i : Fin 4 //
    fourCoordinateSign F i = fourCoordinateSign F 0}
  multiplicity_pos := Nat.card_pos_iff.mpr
    ⟨⟨⟨0, rfl⟩⟩, inferInstance⟩
  uniform_fibre := by
    intro χ
    exact fourCoordinateSign_fibre_card_eq F htrans χ
      (fourCoordinateSign F 0)
  isotype_count_cases := fourCoordinateSign_count_cases F htrans

end BinaryPairFrame

/-- The actual sign-isotype profile of the literal four-pair chart.  No
finite action representative or independently chosen character list enters
this definition. -/
noncomputable def degreeThreeFourBlockSignedIsotypeProfile
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6) :
  DegreeThreeFourBlockSignedIsotypeProfile :=
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  BinaryPairFrame.fourCoordinateSignedIsotypeProfile
    C.frame C.pretransitive

/-- On the literal four-pair chart, the diagonal profile is exactly the
statement that every element of the actual binary block kernel has the same
flip bit on all four blocks.  This is the structural input a reversible
four-marker construction is allowed to use. -/
theorem degreeThreeFourBlockSignedIsotype_eq_one_iff_bits_constant
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6) :
    (degreeThreeFourBlockSignedIsotypeProfile
        block P hr hs hcomponent).isotypeCount = 1 ↔
      let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
      ∀ (k : C.frame.top.ker) (i j : Fin 4),
        C.frame.bits k i = C.frame.bits k j := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  simpa only [degreeThreeFourBlockSignedIsotypeProfile,
    BinaryPairFrame.fourCoordinateSignedIsotypeProfile,
    DegreeThreeFourBlockSignedIsotypeProfile.isotypeCount, C] using
      BinaryPairFrame.fourCoordinateSign_count_eq_one_iff_bits_constant
        C.frame

/-- In the four-isotype branch the four actual coordinate characters of
the literal binary kernel are pairwise distinct.  This is the exact
separation hypothesis used by the signed-ternary irreducibility argument;
no arbitrary list of characters is introduced. -/
theorem degreeThreeFourBlockSignedIsotype_injective_of_count_eq_four
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hfour : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 4) :
    let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
    Function.Injective (BinaryPairFrame.fourCoordinateSign C.frame) := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  simpa only [degreeThreeFourBlockSignedIsotypeProfile,
    BinaryPairFrame.fourCoordinateSignedIsotypeProfile, C] using
      (DegreeThreeFourBlockSignedIsotypeProfile.coordinateSign_injective_of_isotypeCount_eq_four
          (degreeThreeFourBlockSignedIsotypeProfile
            block P hr hs hcomponent) hfour)

/-- Output of the corrected split.  Ordinary source data can be installed
in the current T1 residual catalogue.  Forward data is kept separate until
the ordinary recurrence assembler admits a source-summed forward row. -/
abbrev DegreeThreeFourBlockSignedSourceOrForwardData :=
  PreE7RankTailSourceOrYonedaTopData w U ⊕
    PreE7NumericalRankTailForwardResidualChoice w U

/-- Every valid endpoint of the four-character split.

The diagonal forward constructor takes the exact terminal data itself.  Its
`positiveForward` field is where a diagonal reversible marker construction
must be supplied.  Thus this constructor cannot be inhabited merely from a
bare binary pair route. -/
inductive DegreeThreeFourBlockSignedIsotypeResolution
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (C : DegreeThreeFourBlockSignedIsotypeProfile) : Type 2
  | diagonalOwner
      (hdiagonal : C.isotypeCount = 1)
      (source : ComparatorAbelianTowerCertificateSourceData .s3cent w U)
  | diagonalForward
      (hdiagonal : C.isotypeCount = 1)
      (data : DegreeThreeFourBlockBinaryExactTerminalForwardData
        block P hr hs hcomponent hbinary)
  | twoSignOwner
      (htwo : C.isotypeCount = 2)
      (source : PreE7S3TwoSource w U)
  | singletonOwner
      (hfour : C.isotypeCount = 4)
      (source : PreE7S3ExceptionalSource w U)
  | nonDiagonalDirect
      (hnondiagonal : C.isotypeCount ≠ 1)
      (source : PreE7RankTailSourceOrYonedaTopData w U)
  | nonDiagonalOddForward
      (hnondiagonal : C.isotypeCount ≠ 1)
      (source : PreE7NumericalRankTailForwardResidualChoice w U)

namespace DegreeThreeFourBlockSignedIsotypeResolution

variable
  {hr : Nat.card block.Fibre = 3}
  {hs : Nat.card block.Points = 4}
  {hcomponent : Nat.card block.Component = 6}
  {hbinary : IsPGroup 2
    (degreeThreeFourBlockPairChart block P hr hs hcomponent).action}
  {C : DegreeThreeFourBlockSignedIsotypeProfile}

/-- Forget the structural branch after preserving whether the result is an
ordinary residual source or a genuine forward recurrence. -/
noncomputable def sourceOrForward
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (R : DegreeThreeFourBlockSignedIsotypeResolution
      block P hr hs hcomponent hbinary C) :
    DegreeThreeFourBlockSignedSourceOrForwardData (w := w) (U := U) := by
  cases R with
  | diagonalOwner _ S =>
      exact .inl (.inl (.ordinary .s3cent (.comparator (by decide) S)))
  | diagonalForward _ A =>
      exact .inr (A.forwardResidualChoice block P hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm)
  | twoSignOwner _ S =>
      exact .inl (.inl (.ordinary .s3two
        (.small (PreE7S3LocalAdditiveSource.numericalData S))))
  | singletonOwner _ S =>
      exact .inl (.inl S.toRankTailOwnerSource)
  | nonDiagonalDirect _ S => exact .inl S
  | nonDiagonalOddForward _ S => exact .inr S

/-- If all three held owner constructions have been built from the literal
action, the finite sign-isotype trichotomy selects the correct one. -/
noncomputable def ownerOfCases
    (C : DegreeThreeFourBlockSignedIsotypeProfile)
    (diagonal : C.isotypeCount = 1 →
      ComparatorAbelianTowerCertificateSourceData .s3cent w U)
    (twoSign : C.isotypeCount = 2 → PreE7S3TwoSource w U)
    (singleton : C.isotypeCount = 4 → PreE7S3ExceptionalSource w U) :
    DegreeThreeFourBlockSignedIsotypeResolution
      block P hr hs hcomponent hbinary C := by
  if h₁ : C.isotypeCount = 1 then
    exact .diagonalOwner h₁ (diagonal h₁)
  else if h₂ : C.isotypeCount = 2 then
    exact .twoSignOwner h₂ (twoSign h₂)
  else
    have h₄ : C.isotypeCount = 4 :=
      (C.cases.resolve_left h₁).resolve_left h₂
    exact .singletonOwner h₄ (singleton h₄)

end DegreeThreeFourBlockSignedIsotypeResolution

/-- Narrow concrete theorem boundary.  It retains the actual sign partition
and returns a route whose constructor is compatible with that partition.
Unlike the obsolete universal marker statement, it exposes the non-diagonal
actions which must use an owner, a direct deficit, or an odd continuation. -/
abbrev DegreeThreeFourBlockSignedIsotypeClassification :=
  ∀ {w : ℕ} (U : PreE7NonPairActionClass w)
    (basePoint : Fin w)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (_hK : degreeNineLinearBlockKernel block P ≠ ⊥)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action),
    Nonempty (DegreeThreeFourBlockSignedIsotypeResolution
      block P hr hs hcomponent hbinary
        (degreeThreeFourBlockSignedIsotypeProfile
          block P hr hs hcomponent))

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
