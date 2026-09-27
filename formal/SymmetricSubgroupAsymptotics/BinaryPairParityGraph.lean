import SymmetricSubgroupAsymptotics.BinaryPairAffineChart
import SymmetricSubgroupAsymptotics.PermutationBinaryTwoOrbitSplit

/-! Literal block parities of the full original affine graph.

The exact original kernel equality identifies the quotient of all flip
vectors with the two sums on the original orbit subsets. Both the action
and the cocycle are transported through that reversible map. Every
original lift is retained by the graph-fibre identity; neither a zero
twist nor an original splitting is assumed or concluded.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

open PermutationBinaryTwoOrbitSplit

variable {X I : Type} {U : Subgroup (Equiv.Perm X)} [Finite I]
    (F : BinaryPairFrame U I) (H : Subgroup F.top.range)
    (o₁ o₂ : MulAction.orbitRel.Quotient H I) (hne : o₁≠o₂)
    (hM : F.kernelSpace=twoOrbitAugmentation H o₁ o₂)

/-- Exactly the two original block sums, with no regular block labels. -/
def paritySum : (I → ZMod 2) →ₗ[ZMod 2] (ZMod 2 × ZMod 2) :=
  (orbitSum H o₁).prod (orbitSum H o₂)

/-- The literal correlated kernel is the kernel of the two original
parities, so its quotient has a reversible parity chart. -/
def parityQuotientEquiv : ((I → ZMod 2) ⧸ F.kernelSpace) ≃ₗ[ZMod 2]
    (ZMod 2 × ZMod 2) :=
  (Submodule.quotEquivOfEq F.kernelSpace (twoOrbitAugmentation H o₁ o₂) hM).trans
    ((F.paritySum H o₁ o₂).quotKerEquivOfSurjective
      (jointSum_surjective H o₁ o₂ hne))

@[simp] theorem parityQuotientEquiv_mk (a : I → ZMod 2) :
    F.parityQuotientEquiv H o₁ o₂ hne hM (F.kernelSpace.mkQ a)=F.paritySum H o₁ o₂ a := rfl

/-- The same original top action, transported through the exact parity
chart. Its action on block sums is exposed below. -/
def parityRepresentation : Representation (ZMod 2) F.top.range (ZMod 2 × ZMod 2) :=
  (F.parityQuotientEquiv H o₁ o₂ hne hM).conjRingEquiv.toMonoidHom.comp
    F.affineQuotientRepresentation

theorem parityRepresentation_sum (t : F.top.range) (a : I → ZMod 2) :
    F.parityRepresentation H o₁ o₂ hne hM t (F.paritySum H o₁ o₂ a)=
      F.paritySum H o₁ o₂ (permutationFunctionRepresentation (ZMod 2) F.top.range I t a) := by
  let E := F.parityQuotientEquiv H o₁ o₂ hne hM
  change E (F.affineQuotientRepresentation t (E.symm (E (F.kernelSpace.mkQ a))))=
    E (F.kernelSpace.mkQ (permutationFunctionRepresentation (ZMod 2) F.top.range I t a))
  rw [E.symm_apply_apply]
  rfl

/-- Original extension data in the two literal parity coordinates. -/
def parityClass (t : F.top.range) : ZMod 2 × ZMod 2 :=
  F.parityQuotientEquiv H o₁ o₂ hne hM (F.affineClass t)

theorem parityClass_top (u : U) :
    F.parityClass H o₁ o₂ hne hM (F.top.rangeRestrict u)=
      F.paritySum H o₁ o₂ (F.affineTranslation u) := by
  unfold parityClass
  rw [F.affineClass_top,F.parityQuotientEquiv_mk]

theorem parityClass_mul (t s : F.top.range) :
    F.parityClass H o₁ o₂ hne hM (t*s)=
      F.parityRepresentation H o₁ o₂ hne hM t (F.parityClass H o₁ o₂ hne hM s)+
        F.parityClass H o₁ o₂ hne hM t := by
  unfold parityClass
  rw [F.affineClass_mul,map_add]
  let E := F.parityQuotientEquiv H o₁ o₂ hne hM
  change E (F.affineQuotientRepresentation t (F.affineClass s))+E (F.affineClass t)=
    E (F.affineQuotientRepresentation t (E.symm (E (F.affineClass s))))+E (F.affineClass t)
  rw [E.symm_apply_apply]

/-- The actual parity function is a cocycle, not an assumed split section. -/
def parityCocycle : groupCohomology.cocycles₁ (Rep.of (F.parityRepresentation H o₁ o₂ hne hM)) :=
  ⟨F.parityClass H o₁ o₂ hne hM,
    (groupCohomology.mem_cocycles₁_iff _).mpr (F.parityClass_mul H o₁ o₂ hne hM)⟩

/-- Every original lift and only an original lift satisfies the retained
parity equation. This is an exact original-group graph description. -/
theorem parity_graph_fibre (t : F.top.range) (a : I → ZMod 2) :
    (∃ u : U,F.top.rangeRestrict u=t ∧ F.affineTranslation u=a) ↔
      F.paritySum H o₁ o₂ a=F.parityClass H o₁ o₂ hne hM t := by
  rw [F.affine_graph_fibre]
  exact (F.parityQuotientEquiv H o₁ o₂ hne hM).injective.eq_iff.symm

/-- A true equivalence retaining the same actual top and every original
translation vector, including the complete correlated kernel fibre. -/
def parityGraphEquiv : U ≃
    {p : F.top.range × (I → ZMod 2) //
      F.paritySum H o₁ o₂ p.2=F.parityClass H o₁ o₂ hne hM p.1} :=
  Equiv.ofBijective
    (fun u => ⟨(F.top.rangeRestrict u,F.affineTranslation u),
      (F.parityClass_top H o₁ o₂ hne hM u).symm⟩)
    ⟨fun u v h => F.affineCoordinates_injective (congrArg Subtype.val h),by
      rintro ⟨⟨t,a⟩,ha⟩
      obtain ⟨u,ht,hs⟩ := (F.parity_graph_fibre H o₁ o₂ hne hM t a).mpr ha
      exact ⟨u,Subtype.ext (Prod.ext ht hs)⟩⟩

@[simp] theorem parityGraphEquiv_val (u : U) :
    (F.parityGraphEquiv H o₁ o₂ hne hM u).val=
      (F.top.rangeRestrict u,F.affineTranslation u) := rfl

end SymmetricSubgroupAsymptotics.BinaryPairFrame
