import SymmetricSubgroupAsymptotics.PermutationBinaryLargeSection
import SymmetricSubgroupAsymptotics.OriginalKernelCenter
import SymmetricSubgroupAsymptotics.BinaryPairZeroCutExtension
import SymmetricSubgroupAsymptotics.BinaryPairSectionInvariantBound
import SymmetricSubgroupAsymptotics.BinaryPairSectionCocycleBound
import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport
import SymmetricSubgroupAsymptotics.BinaryCentralCutNumerics
import SymmetricSubgroupAsymptotics.BinaryTransitivePowerSevenCriterion
import SymmetricSubgroupAsymptotics.RepresentationFixedDisplacement

/-! A large actual pair section gives a character entry for the original
quotient. Faithfulness is proved on the actual top range, then transferred
through its actual onto base map. The nonsplit original quotient is retained
in the kernel chart and in the complete central-omega equality. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) (N : Subgroup U) [N.Normal]

/-- The same correlated flip kernel, now acted on by its actual faithful
top range on the original pair labels. -/
def kernelTopPermutationSubrepresentation :
    Subrepresentation (permutationFunctionRepresentation (ZMod 2) F.top.range I) where
  toSubmodule := F.kernelSpace
  apply_mem_toSubmodule t v hv := by
    obtain ⟨u,rfl⟩ := F.top.rangeRestrict_surjective t
    obtain ⟨l,rfl⟩ := hv
    have he : permutationFunctionRepresentation (ZMod 2) F.top.range I
        (F.top.rangeRestrict u) (F.bits l.toMul)=F.bits (MulAut.conjNormal u l.toMul) := by
      funext i
      exact (F.bits_conjNormal u l.toMul i).symm
    change permutationFunctionRepresentation (ZMod 2) F.top.range I
      (F.top.rangeRestrict u) (F.bits l.toMul) ∈ F.kernelSpace
    rw [he]
    exact ⟨Additive.ofMul (MulAut.conjNormal u l.toMul),rfl⟩

/-- This actual quotient intertwiner retains all original coordinate
correlations and the original quotient action. -/
def sectionTopIntertwiner :
    F.kernelTopPermutationSubrepresentation.toRepresentation.IntertwiningMap
      ((F.sectionRepresentation N).comp (F.sectionTopQuotient N)) where
  toLinearMap := (F.normalSpace N).mkQ
  isIntertwining' t := by
    apply LinearMap.ext
    intro v
    obtain ⟨u,rfl⟩ := F.top.rangeRestrict_surjective t
    obtain ⟨l,hl⟩ := F.kernelSpaceHom_bijective.2 (Multiplicative.ofAdd v)
    have hv : (F.kernelSpaceHom l).toAdd=v := congrArg Multiplicative.toAdd hl
    rw [← hv]
    have hcoords : F.kernelTopPermutationSubrepresentation.toRepresentation
        (F.top.rangeRestrict u) (F.kernelSpaceHom l).toAdd=
          (F.kernelSpaceHom (MulAut.conjNormal u l)).toAdd := by
      apply Subtype.ext
      funext i
      exact (F.bits_conjNormal u l i).symm
    change (F.normalSpace N).mkQ
        (F.kernelTopPermutationSubrepresentation.toRepresentation
          (F.top.rangeRestrict u) (F.kernelSpaceHom l).toAdd)=
      F.sectionRepresentation N (F.sectionTopQuotient N (F.top.rangeRestrict u))
        ((F.normalSpace N).mkQ (F.kernelSpaceHom l).toAdd)
    rw [hcoords,F.sectionTopQuotient_apply]
    exact (F.sectionRepresentation_apply N u l).symm

instance largeSection_finite [Finite I] : Finite (F.kernelSpace ⧸ F.normalSpace N) :=
  Finite.of_surjective (F.normalSpace N).mkQ (F.normalSpace N).mkQ_surjective

/-- The large-section argument is applied to the actual faithful top,
not to the original U action on pair labels, which has a kernel. -/
theorem sectionTop_injective_of_large [Finite X] [Finite I]
    [MulAction.IsPretransitive F.top.range I] (hU : IsPGroup 2 U) (i : I)
    (hlarge : Nat.card I<2*Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N)) :
    Function.Injective ((F.sectionRepresentation N).comp (F.sectionTopQuotient N)) :=
  permutationSection_injective_of_half_lt (F.top_isPGroup hU) i
    ((F.sectionRepresentation N).comp (F.sectionTopQuotient N))
    F.kernelTopPermutationSubrepresentation (F.sectionTopIntertwiner N)
    (F.normalSpace N).mkQ_surjective hlarge

theorem sectionTopQuotient_injective_of_large [Finite X] [Finite I]
    [MulAction.IsPretransitive F.top.range I] (hU : IsPGroup 2 U) (i : I)
    (hlarge : Nat.card I<2*Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N)) :
    Function.Injective (F.sectionTopQuotient N) := by
  intro t s h
  apply F.sectionTop_injective_of_large N hU i hlarge
  exact congrArg (F.sectionRepresentation N) h

theorem sectionRepresentation_injective_of_large [Finite X] [Finite I]
    [MulAction.IsPretransitive F.top.range I] (hU : IsPGroup 2 U) (i : I)
    (hlarge : Nat.card I<2*Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N)) :
    Function.Injective (F.sectionRepresentation N) := by
  intro b c h
  obtain ⟨t,rfl⟩ := F.sectionTopQuotient_surjective N b
  obtain ⟨s,rfl⟩ := F.sectionTopQuotient_surjective N c
  exact congrArg (F.sectionTopQuotient N)
    (F.sectionTop_injective_of_large N hU i hlarge h)

/-- Faithfulness also recovers the exact original normal containment;
no top component of N is discarded by a replacement quotient. -/
theorem normal_le_top_ker_of_large [Finite X] [Finite I]
    [MulAction.IsPretransitive F.top.range I] (hU : IsPGroup 2 U) (i : I)
    (hlarge : Nat.card I<2*Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N)) :
    N≤F.top.ker := by
  intro u hu
  have he : F.sectionTopQuotient N (F.top.rangeRestrict u)=
      F.sectionTopQuotient N 1 := by
    rw [F.sectionTopQuotient_apply,map_one]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_right hu)
  have ht := F.sectionTopQuotient_injective_of_large N hU i hlarge he
  exact congrArg Subtype.val ht

/-- The section itself, before the harmless zero-cut quotient, is the
actual kernel of Q=U/N onto B=U/(ker(top) join N). -/
def sectionKernelEquiv : Multiplicative (F.kernelSpace ⧸ F.normalSpace N) ≃*
    (F.zeroCutBase N).ker :=
  binaryPair_sameKernelEquiv (F.sectionMap N) (F.zeroCutKernelMap N)
    (F.sectionMap_surjective N) (F.zeroCutKernelMap_surjective N)
    ((F.sectionMap_ker N).trans (F.zeroCutKernelMap_ker N).symm)

@[simp] theorem sectionKernelEquiv_apply (l : F.top.ker) :
    F.sectionKernelEquiv N (F.sectionMap N l)=F.zeroCutKernelMap N l :=
  binaryPair_sameKernelEquiv_apply _ _ _ _ _ l

def sectionModuleChart : OriginalKernelModuleChart (F.zeroCutBase N)
    (Rep.of (F.sectionRepresentation N)) where
  equiv := F.sectionKernelEquiv N
  conjugate q a := by
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨l,hl⟩ := F.sectionMap_surjective N (Multiplicative.ofAdd a)
    have ha : (F.sectionMap N l).toAdd=a := congrArg Multiplicative.toAdd hl
    rw [← ha,F.zeroCutBase_apply,F.sectionRepresentation_apply]
    have he (m : F.top.ker) :
        (F.sectionKernelEquiv N (F.sectionMap N m) : U ⧸ N)=
          QuotientGroup.mk' N (m:U) :=
      congrArg Subtype.val (F.sectionKernelEquiv_apply N m)
    calc
      _ = QuotientGroup.mk' N (MulAut.conjNormal u l : U) := he (MulAut.conjNormal u l)
      _ = QuotientGroup.mk' N u*QuotientGroup.mk' N (l:U)*(QuotientGroup.mk' N u)⁻¹ := by
        change QuotientGroup.mk' N (u*(l:U)*u⁻¹)=_
        simp only [map_mul,map_inv]
      _ = _ := congrArg (fun z : U ⧸ N =>
        QuotientGroup.mk' N u*z*(QuotientGroup.mk' N u)⁻¹) (he l).symm

theorem binaryCentralOmega_card_of_large [Finite X] [Finite I]
    [MulAction.IsPretransitive F.top.range I] (hU : IsPGroup 2 U) (i : I)
    (hlarge : Nat.card I<2*Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N)) :
    Nat.card (binaryCentralOmega (U ⧸ N))=
      2^Module.finrank (ZMod 2) (F.sectionRepresentation N).invariants :=
  (F.sectionModuleChart N).binaryCentralOmega_card (F.zeroCutBase_surjective N)
    (F.sectionRepresentation_injective_of_large N hU i hlarge)

/-- All original large sections at pair exponent at least four satisfy
the new exact character test, with the whole original quotient retained. -/
def largeSectionSevenCriterion [Finite X] [Finite I]
    [MulAction.IsPretransitive F.top.range I] (hU : IsPGroup 2 U)
    (k : ℕ) (hk : 4≤k) (hI : Nat.card I=2^k)
    (hlarge : 2^k<2*Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N)) :
    BinarySevenCharacterCriterion (U ⧸ N) (Nat.card X) := by
  have hnonempty : Nonempty I := (Nat.card_pos_iff.mp (by
    rw [hI]
    exact pow_pos (by decide) _)).1
  let i : I := Classical.choice hnonempty
  refine {
    dimension := Module.finrank (ZMod 2) (F.sectionRepresentation N).invariants
    cardinal := F.binaryCentralOmega_card_of_large N hU i (by simpa only [hI] using hlarge)
    gap := ?_ }
  rw [F.card_points,hI]
  exact binarySeven_character_gap_of_sixteen_mul_le _ _
    (Nat.mul_pos (by decide) (pow_pos (by decide) _))
    (binary_middle_rank_seven_character_budget k _ hk
      (F.section_invariants_finrank_le_of_top N hU k hI))

/-- In particular the former exceptional t=ell=10 case has a large
actual section, independently of any equality-case classification. -/
theorem section_large_of_joint_ten [Finite X] [Finite I]
    (hI : Nat.card I=32)
    (ht : Module.finrank (ZMod 2) (F.sectionRepresentation N).invariants=10)
    (hell : Module.finrank (ZMod 2)
      (centralQuotientRepresentation (F.sectionRepresentation N)
        (F.sectionRepresentation N).invariants le_rfl).invariants=10) :
    Nat.card I<2*Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N) := by
  have hsub := Submodule.finrank_le
    (centralQuotientRepresentation (F.sectionRepresentation N)
      (F.sectionRepresentation N).invariants le_rfl).invariants
  have hdim := (F.sectionRepresentation N).invariants.finrank_quotient_add_finrank
  rw [hell] at hsub
  rw [ht] at hdim
  rw [hI]
  omega

end SymmetricSubgroupAsymptotics.BinaryPairFrame
