import SymmetricSubgroupAsymptotics.BinaryPairSection
import SymmetricSubgroupAsymptotics.TransitiveBinaryCocycleBound

/-! The original pair-section coefficient is bounded using generators
of its actual transitive top. Both quotient maps and the cut action are
the literal ones attached to the original frame and normal subgroup.
No splitting, generator bound, or cohomology estimate is an input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) (N : Subgroup U)

/-- Every cut quotient is a quotient of the original flip subspace,
which is a literal subspace of the functions on the original pairs. -/
theorem cut_card_le [Finite I]
    (C : Submodule (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N)) :
    Nat.card ((F.kernelSpace ⧸ F.normalSpace N) ⧸ C)≤2^(Nat.card I) := by
  letI : Finite (F.kernelSpace ⧸ F.normalSpace N) :=
    Finite.of_surjective (F.normalSpace N).mkQ (F.normalSpace N).mkQ_surjective
  calc
    Nat.card ((F.kernelSpace ⧸ F.normalSpace N) ⧸ C) ≤
        Nat.card (F.kernelSpace ⧸ F.normalSpace N) :=
      Nat.card_le_card_of_surjective C.mkQ C.mkQ_surjective
    _ ≤ Nat.card F.kernelSpace := Nat.card_le_card_of_surjective
      (F.normalSpace N).mkQ (F.normalSpace N).mkQ_surjective
    _ ≤ Nat.card (I → ZMod 2) := Nat.card_le_card_of_injective
      (fun v : F.kernelSpace => (v : I → ZMod 2)) Subtype.val_injective
    _ = 2^(Nat.card I) := by rw [Nat.card_fun,Nat.card_zmod]

variable [N.Normal]

/-- The actual top range maps onto the original acting quotient
U/(ker(top)∨N), through the first-isomorphism chart for this same top. -/
def sectionTopQuotient : F.top.range →* U ⧸ (F.top.ker⊔N) :=
  (QuotientGroup.lift F.top.ker (QuotientGroup.mk' (F.top.ker⊔N))
    (by rw [QuotientGroup.ker_mk']; exact le_sup_left)).comp
      (QuotientGroup.quotientKerEquivRange F.top).symm.toMonoidHom

theorem sectionTopQuotient_surjective : Function.Surjective (F.sectionTopQuotient N) := by
  exact (QuotientGroup.lift_surjective_of_surjective F.top.ker
    (QuotientGroup.mk' (F.top.ker⊔N))
    (QuotientGroup.mk'_surjective (F.top.ker⊔N))
    (by rw [QuotientGroup.ker_mk']; exact le_sup_left)).comp
      (QuotientGroup.quotientKerEquivRange F.top).symm.surjective

/-- The onto map preserves the original lift, rather than choosing an
unrelated abstract quotient or changing the induced action. -/
@[simp] theorem sectionTopQuotient_apply (u : U) :
    F.sectionTopQuotient N (F.top.rangeRestrict u)=
      QuotientGroup.mk' (F.top.ker⊔N) u := by
  have he : (QuotientGroup.quotientKerEquivRange F.top).symm
      (F.top.rangeRestrict u)=QuotientGroup.mk' F.top.ker u := by
    apply (QuotientGroup.quotientKerEquivRange F.top).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  change QuotientGroup.lift F.top.ker (QuotientGroup.mk' (F.top.ker⊔N))
    (by rw [QuotientGroup.ker_mk']; exact le_sup_left)
    ((QuotientGroup.quotientKerEquivRange F.top).symm (F.top.rangeRestrict u))=
      QuotientGroup.mk' (F.top.ker⊔N) u
  rw [he]
  rfl

/-- The full coefficient for each actual central cut, with its original
representation and cohomology, is bounded by the pair count times the
proved cumulative generating width of the original transitive top. -/
theorem cut_card_mul_firstCohomology_le [Finite X] [Finite I]
    [MulAction.IsPretransitive F.top.range I]
    (hU : IsPGroup 2 U) (k : ℕ) (hdegree : Nat.card I=2^k)
    (C : Submodule (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N))
    (hC : C≤(F.sectionRepresentation N).invariants) :
    Nat.card ((F.kernelSpace ⧸ F.normalSpace N) ⧸ C) *
      Nat.card (groupCohomology.H1 (Rep.of (F.cutRepresentation N C hC))) ≤
        2^((2^k)*(1+binaryCumulativeWidth k)) := by
  letI : Finite (F.kernelSpace ⧸ F.normalSpace N) :=
    Finite.of_surjective (F.normalSpace N).mkQ (F.normalSpace N).mkQ_surjective
  letI : Finite ((F.kernelSpace ⧸ F.normalSpace N) ⧸ C) :=
    Finite.of_surjective C.mkQ C.mkQ_surjective
  have htop : IsPGroup 2 F.top.range :=
    hU.of_surjective F.top.rangeRestrict F.top.rangeRestrict_surjective
  have hH := transitiveBinary_quotient_firstCohomology_card_le k F.top.range
    htop hdegree (F.sectionTopQuotient N) (F.sectionTopQuotient_surjective N)
    (Rep.of (F.cutRepresentation N C hC))
  have hA : Nat.card ((F.kernelSpace ⧸ F.normalSpace N) ⧸ C)≤2^(2^k) := by
    simpa only [hdegree] using F.cut_card_le N C
  calc
    Nat.card ((F.kernelSpace ⧸ F.normalSpace N) ⧸ C) *
        Nat.card (groupCohomology.H1 (Rep.of (F.cutRepresentation N C hC))) ≤
        (2^(2^k))*(2^(2^k))^binaryCumulativeWidth k :=
      Nat.mul_le_mul hA (hH.trans (Nat.pow_le_pow_left hA _))
    _ = 2^((2^k)*(1+binaryCumulativeWidth k)) := by
      rw [Nat.mul_add,Nat.mul_one,pow_add,pow_mul]

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
