import SymmetricSubgroupAsymptotics.BinaryPairEightPhysicalReduction
import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport
import SymmetricSubgroupAsymptotics.BinaryOrderPrunedCoverage
import SymmetricSubgroupAsymptotics.BinaryOrderSevenCharacterFusion
import SymmetricSubgroupAsymptotics.BinarySevenCharacterInstalled
import SymmetricSubgroupAsymptotics.OriginalCentralCutFusion

/-!
# The exact degree-sixteen split frontier

Every original normal axis of a transitive binary action on sixteen
points has a counting-ready central-cut, target-order, or seven-character
entry, unless the same original action is physically conjugate to its
zero affine graph.  The latter residual retains its actual eight-pair
frame and normal axis, and has top order 16 or 32 and source order 1024
or 2048.  Thus the remaining finite theorem concerns only these split
actions; it is not a completeness claim about all transitive actions of
degree sixteen.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryDegree16SplitFrontier

/-- The common direct-fusion interface for every already accepted axis.
All quantities belong to the literal original source and normal subgroup. -/
structure AcceptedEntry (U : Subgroup (Equiv.Perm (Fin 16)))
    (N : Subgroup U) [N.Normal] where
  prefixDegree : ℕ
  markerHalf : ℕ
  liftConstant : ℝ
  gapParameter : ℝ
  momentWeight : {b : ℕ} → Subgroup (Equiv.Perm (Fin b)) → ℝ
  prefix_eq_two_mul : prefixDegree=2*markerHalf
  prefix_lt : prefixDegree<16
  liftConstant_nonneg : 0≤liftConstant
  gapParameter_pos : 0<gapParameter
  moment_le : ∀ b q : ℕ,
    (∑ J : Subgroup (Equiv.Perm (Fin b)),momentWeight J^q)≤
      (subgroupCount (b+q*prefixDegree):ℝ)
  original_envelope : ∀ {b : ℕ}
    (P : Subgroup (U×Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))),
    fusionSurvivingEpiCount U P ⟨N,inferInstance⟩ J≤
      fusionLocalFactor b 8 prefixDegree liftConstant gapParameter*momentWeight J

variable {U : Subgroup (Equiv.Perm (Fin 16))}
    {N : Subgroup U} [N.Normal]

abbrev sectionModule (F : BinaryPairFrame U (Fin 8)) :
    Rep (ZMod 2) (U ⧸ (F.top.ker⊔N)) :=
  Rep.of (F.sectionRepresentation N)

/-- A strict actual central cut is immediately a complete accepted entry.
The displayed cost at most six leaves two full units of slack against the
half-degree eight. -/
def cutEntry (F : BinaryPairFrame U (Fin 8))
    (C : Submodule (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N))
    (hC : C≤(F.sectionRepresentation N).invariants)
    (hcost : (2:ℝ)*Module.finrank (ZMod 2) C+
      4*representationSchurCapacity (F.cutRepresentation N C hC)≤6) :
    AcceptedEntry U N := by
  let A := sectionModule (N := N) F
  let cut : {C : Submodule (ZMod 2) A // C≤A.ρ.invariants} := ⟨C,hC⟩
  have hcost' : (2:ℝ)*Module.finrank (ZMod 2) cut.1+
      4*OriginalCentralCutFusion.capacity A cut≤6 := by
    change (2:ℝ)*Module.finrank (ZMod 2) C+
      4*representationSchurCapacity (F.cutRepresentation N C hC)≤6
    exact hcost
  have hstrict : (2:ℝ)*Module.finrank (ZMod 2) cut.1+
      4*OriginalCentralCutFusion.capacity A cut<(8:ℝ) := by
    linarith
  refine {
    prefixDegree := OriginalCentralCutFusion.prefixDegree A cut 8
    markerHalf := 4+Module.finrank (ZMod 2) cut.1
    liftConstant := OriginalCentralCutFusion.liftConstant A cut
    gapParameter := OriginalCentralCutFusion.gapParameter A cut 16 8
    momentWeight := fun {b} J => OriginalCentralCutFusion.momentWeight A cut J
    prefix_eq_two_mul := ?_
    prefix_lt := OriginalCentralCutFusion.prefixDegree_lt_of_cost A cut 8 hstrict
    liftConstant_nonneg := OriginalCentralCutFusion.liftConstant_nonneg A cut
    gapParameter_pos := OriginalCentralCutFusion.gapParameter_pos_of_cost A cut 8 hstrict
    moment_le := ?_
    original_envelope := ?_ }
  · unfold OriginalCentralCutFusion.prefixDegree
    omega
  · intro b q
    exact OriginalCentralCutFusion.momentWeight_moment_le A cut
      F.top.range.subtype Subtype.val_injective (F.sectionTopQuotient N)
      (F.sectionTopQuotient_surjective N) b q
  · intro b P J
    exact OriginalCentralCutFusion.original_survival_localFactor_le A cut
      (F.zeroCutBase N) (F.zeroCutBase_surjective N) (F.sectionModuleChart N)
      8 8 J (fun f => P (fusionFullGoursatEncode ⟨N,inferInstance⟩ J f).1)

/-- The complete accepted side.  A cut is already flattened to the common
direct interface above.  The other alternative retains the installed
target-order/seven-character certificate, whose direct envelope and all
same-source moments are proved in `BinaryOrderSevenCharacterFusion`. -/
def AcceptedAxis (U : Subgroup (Equiv.Perm (Fin 16)))
    (N : Subgroup U) [N.Normal] : Prop :=
  Nonempty (AcceptedEntry U N) ∨
    Nonempty (BinaryOrderSevenCharacterCertificate U N)

/-- The sole unresolved form.  The point conjugation, original frame,
normal-axis residual, and exact top/source order alternatives are retained. -/
structure SplitResidual (U : Subgroup (Equiv.Perm (Fin 16)))
    (N : Subgroup U) [N.Normal] where
  frame : BinaryPairFrame U (Fin 8)
  residual : frame.EightPairRankTwoResidual N
  conjugator : Fin 8 → ZMod 2
  conjugate_eq :
    U.map (MulAut.conj (frame.physicalFlip conjugator)).toMonoidHom=
      frame.splitAffineAction
  top_order : Nat.card frame.top.range=16 ∨ Nat.card frame.top.range=32
  source_order : Nat.card U=1024 ∨ Nat.card U=2048

/-- Every transitive binary degree-sixteen action is accepted on every
literal original normal axis, except for the exact retained split residual.
No degree-sixteen action catalogue or supplied carrier-completeness premise
is used. -/
theorem axis_frontier (U : Subgroup (Equiv.Perm (Fin 16)))
    [MulAction.IsPretransitive U (Fin 16)] (hU : IsPGroup 2 U)
    (N : Subgroup U) [N.Normal] :
    AcceptedAxis U N ∨ Nonempty (SplitResidual U N) := by
  classical
  obtain ⟨F⟩ := transitiveBinaryPairFrame_nonempty 3 U hU (by norm_num)
  letI : MulAction.IsPretransitive F.top.range (Fin 8) := F.top_pretransitive
  have hI : Nat.card (Fin 8)=8 := Nat.card_fin 8
  rcases F.eight_section_residual_reduction N hU hI with
    hcut | horder | hcharacter | hres
  · obtain ⟨C,hC,hcost⟩ := hcut
    exact Or.inl (Or.inl ⟨cutEntry F C hC hcost⟩)
  · let C : BinaryTargetOrderCertificate U N :=
      BinaryOrderPrunedCoverage.certificateOfQuotientCard U N
        (a := 7) horder.2 (by decide)
    exact Or.inl (Or.inr ⟨.inl C⟩)
  · let C : BinarySevenCharacterCriterion (U⧸N) 16 := by
      simpa only [Nat.card_fin] using hcharacter.some
    exact Or.inl (Or.inr ⟨.inr C⟩)
  · obtain ⟨htop,_,htarget,_,_,hsource⟩ :=
      F.eight_rank_two_original_orders N hU hI hres
    by_cases hsmall : Nat.card F.top.range=8
    · let C : BinaryTargetOrderCertificate U N :=
        BinaryOrderPrunedCoverage.certificateOfQuotientCard U N
          (a := 7) (htarget hsmall) (by decide)
      exact Or.inl (Or.inr ⟨.inl C⟩)
    have hlarge : 8<Nat.card F.top.range := by
      rcases htop with h | h | h <;> omega
    by_cases hp : ∃ h,
        F.rankTwoTranslationParity N hU hI hres hlarge h≠0
    · let C : BinarySevenCharacterCriterion (U⧸N) 16 := by
        simpa only [Nat.card_fin] using
          F.rankTwoNonzeroParitySevenCriterion N hU hI hres hlarge hp
      exact Or.inl (Or.inr ⟨.inr C⟩)
    · have hzero : ∀ h,
          F.rankTwoTranslationParity N hU hI hres hlarge h=0 :=
        fun h => not_ne_iff.mp (fun hh => hp ⟨h,hh⟩)
      obtain ⟨a,ha⟩ :=
        F.rankTwo_zero_first_parity_physical_conjugate N hU hI hres hlarge hzero
      have ht : Nat.card F.top.range=16 ∨ Nat.card F.top.range=32 := by
        rcases htop with h | h | h
        · exact False.elim (hsmall h)
        · exact Or.inl h
        · exact Or.inr h
      have hs : Nat.card U=1024 ∨ Nat.card U=2048 := by
        rcases ht with ht | ht
        · left
          omega
        · right
          omega
      exact Or.inr ⟨⟨F,hres,a,ha,ht,hs⟩⟩

end SymmetricSubgroupAsymptotics.BinaryDegree16SplitFrontier

end
