import SymmetricSubgroupAsymptotics.BinaryPairSectionInvariantBound
import SymmetricSubgroupAsymptotics.BinaryPairLargeSectionCharacter
import SymmetricSubgroupAsymptotics.BinaryNonelementaryPermutationHead

/-! Full invariant spaces of the SAME original normal pair sections.
The invariant section is a trivial quotient of its actual preimage in the
natural module. Thus the nonelementary quarter bound applies without
asserting that the section itself embeds in the natural module. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) (N : Subgroup U) [N.Normal]

/-- The full original invariant section has the nonelementary quarter
bound, independently of the top image of the original normal N. -/
theorem section_invariants_finrank_le_quarter_of_not_elementary
    [Finite X] [Finite I] [MulAction U I] [MulAction.IsPretransitive U I]
    (hact : ∀ (u : U) (i : I), u • i = F.top u i)
    (hU : IsPGroup 2 U)
    (hnon : ¬ BinarySquareActionStructure.SquaresActTrivially (G := U) (X := I)) :
    Module.finrank (ZMod 2) (F.sectionRepresentation N).invariants ≤ Nat.card I / 4 := by
  let S := (F.sectionRepresentation N).invariants
  let q := (F.normalSpace N).mkQ
  let P : Submodule (ZMod 2) F.kernelSpace := S.comap q
  let K := F.kernelOriginalSubrepresentation hact
  have hfixed (u : U) (v : F.kernelSpace) (hv : v∈P) :
      q (K.toRepresentation u v)=q v :=
    (F.sectionMkQ_equivariant N hact u v).trans
      (hv (QuotientGroup.mk' (F.top.ker⊔N) u))
  let M : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U I) := {
    toSubmodule := P.map F.kernelSpace.subtype
    apply_mem_toSubmodule := by
      intro u v hv
      obtain ⟨v,hv,rfl⟩ := hv
      refine ⟨K.toRepresentation u v,?_,rfl⟩
      change q (K.toRepresentation u v)∈S
      rw [hfixed u v hv]
      exact hv }
  let e : P ≃ₗ[ZMod 2] M.toSubmodule := F.kernelSpace.equivSubtypeMap P
  let qP : P →ₗ[ZMod 2] S := (q.comp P.subtype).codRestrict S (fun v => v.property)
  have hqP : Function.Surjective qP := by
    intro s
    obtain ⟨v,hv⟩ := (F.normalSpace N).mkQ_surjective (s : F.kernelSpace ⧸ F.normalSpace N)
    have hvP : v∈P := by
      change q v∈S
      rw [hv]
      exact s.property
    exact ⟨⟨v,hvP⟩,Subtype.ext hv⟩
  let qM : M.toSubmodule →ₗ[ZMod 2] S := qP.comp e.symm.toLinearMap
  have hqM : Function.Surjective qM := hqP.comp e.symm.surjective
  have htrivial : ∀ (u : U) (m : M.toSubmodule),
      qM (M.toRepresentation u m)=qM m := by
    intro u m
    apply Subtype.ext
    change q (e.symm (M.toRepresentation u m) : F.kernelSpace)=
      q (e.symm m : F.kernelSpace)
    have he : (e.symm (M.toRepresentation u m) : F.kernelSpace)=
        K.toRepresentation u (e.symm m : F.kernelSpace) := by
      apply Subtype.ext
      rfl
    rw [he]
    exact hfixed u (e.symm m : F.kernelSpace) (e.symm m).property
  let q' : M.toRepresentation.Coinvariants →ₗ[ZMod 2] S :=
    Representation.Coinvariants.lift M.toRepresentation qM (by
      intro u
      apply LinearMap.ext
      exact htrivial u)
  have hq' : Function.Surjective q' := by
    intro s
    obtain ⟨m, hm⟩ := hqM s
    exact ⟨Representation.Coinvariants.mk M.toRepresentation m, hm⟩
  have hdim := LinearMap.finrank_le_finrank_of_surjective hq'
  rw [← representationHead_finrank_eq_coinvariants] at hdim
  exact hdim.trans
    (twoGroup_permutationSubrepresentationHead_le_quarter_of_not_elementary hU hnon M)


/-- If the original eight-pair section has dimension greater than four,
the actual quotient center has order at most four. No top component of N
is removed; large-section faithfulness proves any needed containment. -/
theorem large_eight_section_center_card_le_four
    [Finite X] [Finite I] [MulAction U I] [MulAction.IsPretransitive U I]
    [MulAction.IsPretransitive F.top.range I]
    (hact : ∀ (u : U) (i : I), u • i = F.top u i)
    (hU : IsPGroup 2 U)
    (hnon : ¬ BinarySquareActionStructure.SquaresActTrivially (G := U) (X := I))
    (hdegree : Nat.card I = 8)
    (hlarge : 4 < Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N)) :
    Nat.card (Subgroup.center (U ⧸ N)) ≤ 4 := by
  have hpos : 0 < Nat.card I := by rw [hdegree]; decide
  let i : I := Classical.choice (Nat.card_pos_iff.mp hpos).1
  have hinj := F.sectionRepresentation_injective_of_large N hU i (by rw [hdegree]; omega)
  have hc := Nat.card_congr
    ((F.sectionModuleChart N).invariantsCenterEquiv
      (F.zeroCutBase_surjective N) hinj)
  have hdim := F.section_invariants_finrank_le_quarter_of_not_elementary N hact hU hnon
  rw [hdegree] at hdim
  calc
    Nat.card (Subgroup.center (U ⧸ N)) =
        Nat.card (F.sectionRepresentation N).invariants := hc.symm
    _ = 2 ^ Module.finrank (ZMod 2) (F.sectionRepresentation N).invariants := by
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2)
          (V := (F.sectionRepresentation N).invariants))
    _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega)
    _ = 4 := by norm_num

end SymmetricSubgroupAsymptotics.BinaryPairFrame
