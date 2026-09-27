import SymmetricSubgroupAsymptotics.BinaryPairLargeSectionCharacter
import SymmetricSubgroupAsymptotics.PermutationBinaryRankTwoOrbits

/-! Residual sections on the actual original top range.

The original map T=range(top) onto B=U/(ker(top) join N) is retained.
Its surjectivity preserves the whole fixed space and all literal central
cut fixed spaces. The original N is not replaced by its intersection
with the flip kernel: its entire top image is retained inside the actual
section-action kernel. Only proved faithfulness can force that image to
vanish.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

section Onto

variable {k G B A : Type} [Field k] [Group G] [Group B]
    [AddCommGroup A] [Module k A]
    (ρ : Representation k B A) (π : G →* B) (hπ : Function.Surjective π)

include hπ

theorem representation_invariants_comp_onto :
    Representation.invariants (ρ.comp π)=ρ.invariants := by
  ext a
  constructor
  · intro ha b
    obtain ⟨g,rfl⟩ := hπ b
    exact ha g
  · intro ha g
    exact ha (π g)

theorem centralQuotient_invariants_comp_onto
    (C : Submodule k A) (hC : C≤ρ.invariants) :
    (centralQuotientRepresentation (ρ.comp π) C
      (fun a ha g => hC ha (π g))).invariants=
        (centralQuotientRepresentation ρ C hC).invariants := by
  ext a
  constructor
  · intro ha b
    obtain ⟨g,rfl⟩ := hπ b
    exact ha g
  · intro ha g
    exact ha (π g)

theorem fullFixedQuotient_finrank_comp_onto :
    Module.finrank k (centralQuotientRepresentation (ρ.comp π)
      (Representation.invariants (ρ.comp π)) le_rfl).invariants=
        Module.finrank k (centralQuotientRepresentation ρ ρ.invariants le_rfl).invariants := by
  have hinv := representation_invariants_comp_onto ρ π hπ
  have hcut : Representation.invariants (ρ.comp π)≤ρ.invariants := hinv.le
  have he := centralQuotient_invariants_comp_onto ρ π hπ
    (Representation.invariants (ρ.comp π)) hcut
  have htransport (S : Submodule k A) (hS : S≤ρ.invariants) (hS' : S=ρ.invariants) :
      Module.finrank k (centralQuotientRepresentation ρ S hS).invariants=
        Module.finrank k (centralQuotientRepresentation ρ ρ.invariants le_rfl).invariants := by
    subst S
    rfl
  have he' := congrArg (fun S : Submodule k
      (A ⧸ Representation.invariants (ρ.comp π)) =>
    Module.finrank k S) he
  change Module.finrank k (centralQuotientRepresentation (ρ.comp π)
      (Representation.invariants (ρ.comp π)) le_rfl).invariants=
    Module.finrank k (centralQuotientRepresentation ρ
      (Representation.invariants (ρ.comp π)) hcut).invariants at he'
  exact he'.trans (htransport _ hcut hinv)

end Onto

namespace BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) (N : Subgroup U) [N.Normal]

/-- The section acted on by its actual top permutation range. -/
abbrev sectionTopRepresentation :
    Representation (ZMod 2) F.top.range (F.kernelSpace ⧸ F.normalSpace N) :=
  (F.sectionRepresentation N).comp (F.sectionTopQuotient N)

theorem sectionTop_invariants_eq :
    (F.sectionTopRepresentation N).invariants=(F.sectionRepresentation N).invariants :=
  representation_invariants_comp_onto (F.sectionRepresentation N)
    (F.sectionTopQuotient N) (F.sectionTopQuotient_surjective N)

theorem sectionTop_fixed_quotient_finrank_eq :
    Module.finrank (ZMod 2) (centralQuotientRepresentation (F.sectionTopRepresentation N)
      (F.sectionTopRepresentation N).invariants le_rfl).invariants=
        Module.finrank (ZMod 2) (centralQuotientRepresentation (F.sectionRepresentation N)
          (F.sectionRepresentation N).invariants le_rfl).invariants :=
  fullFixedQuotient_finrank_comp_onto (F.sectionRepresentation N)
    (F.sectionTopQuotient N) (F.sectionTopQuotient_surjective N)

/-- The full original top image of N is retained. No N=K intersect N
or quotient-monotonicity assertion is made. -/
theorem normal_top_image_le_sectionTop_kernel :
    N.map F.top.rangeRestrict≤(F.sectionTopRepresentation N).ker := by
  rintro _ ⟨u,hu,rfl⟩
  change F.sectionRepresentation N (F.sectionTopQuotient N (F.top.rangeRestrict u))=1
  have hq : QuotientGroup.mk' (F.top.ker⊔N) u=1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_right hu)
  rw [F.sectionTopQuotient_apply,hq,map_one]

theorem normal_le_top_ker_of_sectionTop_injective
    (hfaithful : Function.Injective (F.sectionTopRepresentation N)) : N≤F.top.ker := by
  intro u hu
  have hm := F.normal_top_image_le_sectionTop_kernel N ⟨u,hu,rfl⟩
  have hm' : F.sectionTopRepresentation N (F.top.rangeRestrict u)=1 := hm
  have he : F.top.rangeRestrict u=1 := hfaithful
    (show F.sectionTopRepresentation N (F.top.rangeRestrict u)=
      F.sectionTopRepresentation N 1 from hm'.trans (map_one _).symm)
  exact congrArg Subtype.val he

theorem sectionRepresentation_injective_of_sectionTop_injective
    (hfaithful : Function.Injective (F.sectionTopRepresentation N)) :
    Function.Injective (F.sectionRepresentation N) := by
  intro b c h
  obtain ⟨t,rfl⟩ := F.sectionTopQuotient_surjective N b
  obtain ⟨s,rfl⟩ := F.sectionTopQuotient_surjective N c
  exact congrArg (F.sectionTopQuotient N) (hfaithful h)

/-- Faithfulness of the original top action accepts the unchanged
original quotient at eight pairs; no large-section inequality is needed. -/
def faithfulSectionTopSevenCriterion_of_eight [Finite X] [Finite I]
    [MulAction.IsPretransitive F.top.range I] (hU : IsPGroup 2 U)
    (hI : Nat.card I=8)
    (hfaithful : Function.Injective (F.sectionTopRepresentation N)) :
    BinarySevenCharacterCriterion (U ⧸ N) (Nat.card X) := by
  refine {
    dimension := Module.finrank (ZMod 2) (F.sectionRepresentation N).invariants
    cardinal := (F.sectionModuleChart N).binaryCentralOmega_card
      (F.zeroCutBase_surjective N)
      (F.sectionRepresentation_injective_of_sectionTop_injective N hfaithful)
    gap := ?_ }
  rw [F.card_points,hI]
  apply binarySeven_character_gap_of_sixteen_mul_le _ _ (by decide)
  have ht := F.section_invariants_finrank_le_of_top N hU 3 (by simpa using hI)
  norm_num at ht
  omega

/-- The complete rank-two residual is instantiated on the actual
faithful permutation top and then transported back to the original cut.
The second alternative retains the actual image of all of N. -/
theorem eight_rank_two_cut_or_original_kernel [Finite X] [Finite I]
    [MulAction.IsPretransitive F.top.range I] (hU : IsPGroup 2 U)
    (hI : Nat.card I=8)
    (hd : Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N)=4)
    (ht : Module.finrank (ZMod 2) (F.sectionRepresentation N).invariants=2)
    (hell : Module.finrank (ZMod 2) (centralQuotientRepresentation (F.sectionRepresentation N)
      (F.sectionRepresentation N).invariants le_rfl).invariants=2) :
    (∃ (C : Submodule (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N))
      (hC : C≤(F.sectionRepresentation N).invariants),
      (2:ℝ)*Module.finrank (ZMod 2) C+
        4*representationSchurCapacity (F.cutRepresentation N C hC)≤6) ∨
    (Nonempty (RepresentationBinaryCommonCharacter.TwoBlockCharacter
        (F.sectionTopRepresentation N)) ∧
      Nat.card (MulAction.orbitRel.Quotient (F.sectionTopRepresentation N).ker I)=2 ∧
      (∀ o : MulAction.orbitRel.Quotient (F.sectionTopRepresentation N).ker I,
        Nat.card o.orbit=4) ∧
      N.map F.top.rangeRestrict≤(F.sectionTopRepresentation N).ker) := by
  have htTop : Module.finrank (ZMod 2) (F.sectionTopRepresentation N).invariants=2 := by
    rw [F.sectionTop_invariants_eq,ht]
  have hDTop : Module.finrank (ZMod 2)
      (displacementSlice (F.sectionTopRepresentation N) (F.sectionTopRepresentation N).invariants)=2 := by
    rw [displacementSlice_invariants_finrank,F.sectionTop_fixed_quotient_finrank_eq,hell]
  rcases RepresentationBinaryCommonCharacter.central_cut_or_twoBlockCharacter
    (F.sectionTopRepresentation N) hd htTop hDTop with hcut | hdata
  · obtain ⟨C,hC,_,hCdim,hquot⟩ := hcut
    have hCbase : C≤(F.sectionRepresentation N).invariants :=
      hC.trans (F.sectionTop_invariants_eq N).le
    have he := centralQuotient_invariants_comp_onto (F.sectionRepresentation N)
      (F.sectionTopQuotient N) (F.sectionTopQuotient_surjective N) C hCbase
    have he' := congrArg (fun S : Submodule (ZMod 2)
      ((F.kernelSpace ⧸ F.normalSpace N) ⧸ C) => Module.finrank (ZMod 2) S) he
    have hbase : Module.finrank (ZMod 2) (F.cutRepresentation N C hCbase).invariants=1 :=
      he'.symm.trans hquot
    letI : Finite ((F.kernelSpace ⧸ F.normalSpace N) ⧸ C) :=
      Finite.of_surjective C.mkQ C.mkQ_surjective
    apply Or.inl
    refine ⟨C,hCbase,?_⟩
    rw [pGroup_representationSchurCapacity (hU.to_quotient (F.top.ker⊔N)),hCdim,hbase]
    norm_num
  · obtain ⟨data⟩ := hdata
    have hnonempty : Nonempty I := (Nat.card_pos_iff.mp (by rw [hI]; decide)).1
    let i : I := Classical.choice hnonempty
    have horbits := permutationBinary_twoBlockCharacter_orbits (F.top_isPGroup hU)
      i hI (F.sectionTopRepresentation N) F.kernelTopPermutationSubrepresentation
      (F.sectionTopIntertwiner N) (F.normalSpace N).mkQ_surjective hd data
    exact Or.inr ⟨⟨data⟩,horbits.1,horbits.2,F.normal_top_image_le_sectionTop_kernel N⟩

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
