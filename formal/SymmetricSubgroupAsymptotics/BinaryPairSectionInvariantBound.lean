import SymmetricSubgroupAsymptotics.BinaryPairSection
import SymmetricSubgroupAsymptotics.BinaryPairKernelHead
import SymmetricSubgroupAsymptotics.PermutationBinaryTrivialSection
import SymmetricSubgroupAsymptotics.BinarySubspaceTupleCount

/-! The full invariant space of an original pair section is a trivial
quotient of its original preimage in the binary permutation module.
It is not assumed to embed in that module. Its dimension bound counts
all literal central cuts, without selecting an admissible cut menu. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) (N : Subgroup U) [N.Normal]

section OriginalAction

variable [MulAction U I] (hact : ∀ (u : U) (i : I), u • i=F.top u i)

/-- The original section projection intertwines all original U
conjugations, in the retained correlated kernel coordinates. -/
theorem sectionMkQ_equivariant (u : U) (v : F.kernelSpace) :
    (F.normalSpace N).mkQ ((F.kernelOriginalSubrepresentation hact).toRepresentation u v)=
      F.sectionRepresentation N (QuotientGroup.mk' (F.top.ker⊔N) u)
        ((F.normalSpace N).mkQ v) := by
  obtain ⟨l,hl⟩ := F.kernelSpaceHom_bijective.2 (Multiplicative.ofAdd v)
  have hv : (F.kernelSpaceHom l).toAdd=v := congrArg Multiplicative.toAdd hl
  rw [← hv]
  have hcoords : (F.kernelOriginalSubrepresentation hact).toRepresentation u
      (F.kernelSpaceHom l).toAdd=(F.kernelSpaceHom (MulAut.conjNormal u l)).toAdd := by
    apply Subtype.ext
    exact F.originalCoordinateAction_bits hact u l
  rw [hcoords]
  exact (F.sectionRepresentation_apply N u l).symm

include hact in
/-- The whole invariant section is an actual invariant quotient of a
subrepresentation of the ORIGINAL permutation module, so Boolean width
applies without any monotonicity claim for section heads. -/
theorem section_invariants_finrank_le [Finite X] [Finite I]
    [MulAction.IsPretransitive U I] (hU : IsPGroup 2 U)
    (k : ℕ) (hdegree : Nat.card I=2^k) (i : I) :
    Module.finrank (ZMod 2) (F.sectionRepresentation N).invariants≤k.choose (k/2) := by
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
  exact twoGroup_permutation_trivial_quotient_finrank_le hU k hdegree i M qM hqM htrivial

include hact in
/-- All original central cuts are counted, through the exact submodule
lattice of the whole invariant space; no finite cut list is assumed. -/
theorem section_centralCuts_card_le [Finite X] [Finite I]
    [MulAction.IsPretransitive U I] (hU : IsPGroup 2 U)
    (k : ℕ) (hdegree : Nat.card I=2^k) (i : I) :
    Nat.card {C : Submodule (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N) //
      C≤(F.sectionRepresentation N).invariants}≤2^(k.choose (k/2)*k.choose (k/2)) := by
  let S := (F.sectionRepresentation N).invariants
  letI : Finite (F.kernelSpace ⧸ F.normalSpace N) :=
    Finite.of_surjective (F.normalSpace N).mkQ (F.normalSpace N).mkQ_surjective
  calc
    Nat.card {C : Submodule (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N) // C≤S} =
        Nat.card (Submodule (ZMod 2) S) :=
      Nat.card_congr (Submodule.MapSubtype.orderIso (p := S)).symm.toEquiv
    _ ≤ 2^(k.choose (k/2)*k.choose (k/2)) :=
      binarySubmodule_card_le_of_finrank_le S (k.choose (k/2))
        (F.section_invariants_finrank_le N hact hU k hdegree i)

end OriginalAction

/-- Top-range transitivity supplies the needed original U action on
the same pair labels, via the given top homomorphism. -/
theorem section_invariants_finrank_le_of_top [Finite X] [Finite I]
    [MulAction.IsPretransitive F.top.range I] (hU : IsPGroup 2 U)
    (k : ℕ) (hdegree : Nat.card I=2^k) :
    Module.finrank (ZMod 2) (F.sectionRepresentation N).invariants≤k.choose (k/2) := by
  letI : MulAction U I := MulAction.compHom I F.top
  letI : MulAction.IsPretransitive U I := ⟨by
    intro i j
    obtain ⟨t,ht⟩ := MulAction.exists_smul_eq F.top.range i j
    obtain ⟨u,rfl⟩ := F.top.rangeRestrict_surjective t
    exact ⟨u,ht⟩⟩
  have hI : Nonempty I := (Nat.card_pos_iff.mp (by
    rw [hdegree]
    exact pow_pos (by decide) _)).1
  exact F.section_invariants_finrank_le N (fun _ _ => rfl) hU k hdegree
    (Classical.choice hI)

/-- Complete central-cut count using only the actual transitive top,
the original binary group, and the original pair degree. -/
theorem section_centralCuts_card_le_of_top [Finite X] [Finite I]
    [MulAction.IsPretransitive F.top.range I] (hU : IsPGroup 2 U)
    (k : ℕ) (hdegree : Nat.card I=2^k) :
    Nat.card {C : Submodule (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N) //
      C≤(F.sectionRepresentation N).invariants}≤2^(k.choose (k/2)*k.choose (k/2)) := by
  let S := (F.sectionRepresentation N).invariants
  letI : Finite (F.kernelSpace ⧸ F.normalSpace N) :=
    Finite.of_surjective (F.normalSpace N).mkQ (F.normalSpace N).mkQ_surjective
  calc
    Nat.card {C : Submodule (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N) // C≤S} =
        Nat.card (Submodule (ZMod 2) S) :=
      Nat.card_congr (Submodule.MapSubtype.orderIso (p := S)).symm.toEquiv
    _ ≤ 2^(k.choose (k/2)*k.choose (k/2)) :=
      binarySubmodule_card_le_of_finrank_le S (k.choose (k/2))
        (F.section_invariants_finrank_le_of_top N hU k hdegree)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
