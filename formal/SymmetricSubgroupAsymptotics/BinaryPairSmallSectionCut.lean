import SymmetricSubgroupAsymptotics.BinarySmallSectionCentralCut
import SymmetricSubgroupAsymptotics.BinaryPairSectionInvariantBound

/-! Install the proved small-section central cut on each literal original
pair frame and normal axis. The section, acting quotient and quotient-cut
representation are the existing original objects. Inflation is only along
the actual onto original quotient, and does not change Schur capacity. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) (N : Subgroup U) [N.Normal]

/-- The existing exact section with its action inflated to original U. -/
def sectionOriginalRepresentation : Representation (ZMod 2) U
    (F.kernelSpace ⧸ F.normalSpace N) :=
  (F.sectionRepresentation N).comp (QuotientGroup.mk' (F.top.ker⊔N))

theorem sectionOriginalRepresentation_invariants :
    (F.sectionOriginalRepresentation N).invariants = (F.sectionRepresentation N).invariants := by
  ext a
  constructor
  · intro ha g
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (F.top.ker⊔N) g
    exact ha u
  · intro ha u
    exact ha (QuotientGroup.mk' (F.top.ker⊔N) u)

section OriginalAction

variable [MulAction U I] (hact : ∀ (u : U) (i : I), u • i=F.top u i)

/-- The onto original section map intertwines all original U actions;
its source is the actual correlated kernel subrepresentation. -/
def sectionOriginalProjection :
    (F.kernelOriginalSubrepresentation hact).toRepresentation.IntertwiningMap
      (F.sectionOriginalRepresentation N) where
  toLinearMap := (F.normalSpace N).mkQ
  isIntertwining' u := by
    apply LinearMap.ext
    intro v
    exact F.sectionMkQ_equivariant N hact u v

theorem sectionOriginalProjection_surjective :
    Function.Surjective (F.sectionOriginalProjection N hact) :=
  (F.normalSpace N).mkQ_surjective

include hact in
/-- Every small actual original section has a strict cut with cost at
most its pair degree minus two. No normal-axis capacity is supplied. -/
theorem exists_small_section_cut [Finite X] [Finite I]
    [MulAction.IsPretransitive U I] (hU : IsPGroup 2 U)
    (k : ℕ) (hk : 4≤k) (hI : Nat.card I=2^k) (i : I)
    (hsmall : 2*Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N)≤2^k) :
    ∃ (C : Submodule (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N))
      (hC : C≤(F.sectionRepresentation N).invariants),
      (2:ℝ)*Module.finrank (ZMod 2) C+
        4*representationSchurCapacity (F.cutRepresentation N C hC)+2≤(2:ℝ)^k := by
  let A := F.kernelSpace ⧸ F.normalSpace N
  letI : Finite A :=
    Finite.of_surjective (F.normalSpace N).mkQ (F.normalSpace N).mkQ_surjective
  obtain ⟨C,hC,hcost⟩ := binary_small_permutationSection_exists_central_cut_capacity
    (F.sectionOriginalRepresentation N) hU (F.kernelOriginalSubrepresentation hact)
    (F.sectionOriginalProjection N hact) (F.sectionOriginalProjection_surjective N hact)
    i k hk hI hsmall
  have hCB : C≤(F.sectionRepresentation N).invariants := by
    rw [← F.sectionOriginalRepresentation_invariants N]
    exact hC
  refine ⟨C,hCB,?_⟩
  have he : centralQuotientRepresentation (F.sectionOriginalRepresentation N) C hC =
      (F.cutRepresentation N C hCB).comp (QuotientGroup.mk' (F.top.ker⊔N)) := by
    apply MonoidHom.ext
    intro u
    apply LinearMap.ext
    intro v
    obtain ⟨a,rfl⟩ := C.mkQ_surjective v
    rfl
  rw [he,representationSchurCapacity_comp (QuotientGroup.mk' (F.top.ker⊔N))
    (QuotientGroup.mk'_surjective (F.top.ker⊔N))] at hcost
  exact hcost

end OriginalAction

/-- Actual top transitivity supplies the original action on the same
pair labels. No faithful action of the quotient B is requested. -/
theorem exists_small_section_cut_of_top [Finite X] [Finite I]
    [MulAction.IsPretransitive F.top.range I] (hU : IsPGroup 2 U)
    (k : ℕ) (hk : 4≤k) (hI : Nat.card I=2^k)
    (hsmall : 2*Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N)≤2^k) :
    ∃ (C : Submodule (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N))
      (hC : C≤(F.sectionRepresentation N).invariants),
      (2:ℝ)*Module.finrank (ZMod 2) C+
        4*representationSchurCapacity (F.cutRepresentation N C hC)+2≤(2:ℝ)^k := by
  letI : MulAction U I := MulAction.compHom I F.top
  letI : MulAction.IsPretransitive U I := ⟨by
    intro i j
    obtain ⟨t,ht⟩ := MulAction.exists_smul_eq F.top.range i j
    obtain ⟨u,rfl⟩ := F.top.rangeRestrict_surjective t
    exact ⟨u,ht⟩⟩
  have hnonempty : Nonempty I := (Nat.card_pos_iff.mp (by
    rw [hI]
    exact pow_pos (by decide) _)).1
  exact F.exists_small_section_cut N (fun _ _ => rfl) hU k hk hI
    (Classical.choice hnonempty) hsmall

end SymmetricSubgroupAsymptotics.BinaryPairFrame
