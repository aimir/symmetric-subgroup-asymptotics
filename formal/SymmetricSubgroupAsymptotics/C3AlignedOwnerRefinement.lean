import SymmetricSubgroupAsymptotics.C3PhysicalOwnerAlignedContinuation

/-!
# Intrinsic numerical owners on aligned high-C3 cells

The coarse first-owner branch is enough to recover the exact numerical owner
once its high normal pair lives on the same retained action.  Degree six
refines to the odd-index-two or cyclic-binary owner; degree twelve refines to
the prime-base or binary-nine owner.  This is the six-way case split to which
the remaining local counting theorems attach.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- Exact numerical owner content forced by a coarse branch on one retained
literal action. -/
def C3HighAlignedOwnerRefinement {w : ℕ} (k : C3PhysicalOwnerKind)
    (U : Subgroup (Equiv.Perm (Fin w))) : Prop :=
  match k with
  | .ternaryPGroup => IsPGroup 3 U
  | .naturalA4 => IsNaturalA4Action
      U (Fin w)
  | .degreeSix =>
      Nonempty (C1OddIndexTwoOwnerWitness U) ∨
      Nonempty (C1CyclicBinaryModuleOwnerWitness U)
  | .degreeTwelve =>
      IsC1TernaryPrimeBaseOwner U ∨
      IsC1BinaryNineTopOwner U (Fin w)

/-- Exact owner content forced by the coarse branch on an aligned finite
continuation cell. -/
def C3HighAlignedBranchRefinement
    (j : C3HighAlignedFirstOwnerIndex) : Prop :=
  C3HighAlignedOwnerRefinement (c3PhysicalOwnerKindEquiv j.1.2.1)
    (c3HighAlignedFirstOwnerAction j)

/-- A literal aligned transitive action refines intrinsically to the exact
numerical owner selected by its coarse branch. -/
theorem C3HighAlignedOwnerAction.refinement
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    {w : ℕ} (k : C3PhysicalOwnerKind)
    (U : Subgroup (Equiv.Perm (Fin w)))
    [MulAction.IsPretransitive U (Fin w)]
    (h : C3HighAlignedOwnerAction k U) :
    C3HighAlignedOwnerRefinement k U := by
  rcases h.1 with ⟨N, hN, hHigh, hEarlier⟩
  letI : N.Normal := hN
  have hHigh' : 3 * Nat.card (Fin w) <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) := by
    simpa using hHigh
  cases k with
  | ternaryPGroup =>
      exact h.2
  | naturalA4 =>
      exact h.2
  | degreeSix =>
      exact degreeSix_high_structuralOwner hPrimitive N h.2 hHigh'
  | degreeTwelve =>
      exact OriginalMinimalBlock.degreeTwelve_high_structuralOwner
        hChief hWeight hPrimitive h18 N h.2 hHigh'

/-- The retained high pair and the coarse branch certificate recover the
correct intrinsic numerical owner on that same literal action. -/
theorem c3HighAligned_branchRefinement
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (j : C3HighAlignedFirstOwnerIndex) :
    C3HighAlignedBranchRefinement j := by
  rcases j with ⟨⟨d, owner, i⟩, hj⟩
  have hj' : C3HighAlignedOwnerAction (c3PhysicalOwnerKindEquiv owner)
      i.representative := by
    simpa only [c3HighFirstOwnerAction, c3HighFirstOwnerWidth] using hj
  have h := hj'.refinement hChief hWeight hPrimitive h18
    (c3PhysicalOwnerKindEquiv owner) i.representative
  simpa only [C3HighAlignedBranchRefinement,
    c3HighAlignedFirstOwnerAction, c3HighAlignedFirstOwnerWidth,
    c3HighFirstOwnerAction, c3HighFirstOwnerWidth] using h

end SymmetricSubgroupAsymptotics

end
