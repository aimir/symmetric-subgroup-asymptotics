import SymmetricSubgroupAsymptotics.ActualWreathElementaryCoordinateEmbedding
import SymmetricSubgroupAsymptotics.WreathKernelSubquotientFaithfulness
import SymmetricSubgroupAsymptotics.OriginalKernelSectionGeneration

/-! The faithful retained-constituent corollary is project-owned and is
proved from raw modular Clifford plus actual compression coordinates.
No faithful-subquotient or normal-envelope premise is retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CliffordHomogeneousRestriction
open PermutationalWreathProduct OriginalKernelModuleChart

/-- Projection onto the SAME original normal section, over an arbitrary prime field. -/
private def primeSectionProjectionOnBase
    {p : ℕ} {G B : Type} [Group G] [Group B]
    (pi : G →* B) (A : Rep (ZMod p) B) (E : OriginalKernelModuleChart pi A)
    (N : Subgroup G) [N.Normal] (hpi : Function.Surjective pi) :
    Representation.IntertwiningMap A.ρ
      ((show Representation (ZMod p) (G ⧸ (pi.ker ⊔ N)) (E.sectionModule pi A N) from
        (E.sectionRepresentation pi A N).ρ).comp (labelTop pi N hpi)) where
  toLinearMap := (E.sectionProjection pi A N).toLinearMap
  isIntertwining' b := by
    apply LinearMap.ext
    intro v
    obtain ⟨g,rfl⟩ := hpi b
    change E.sectionProjection pi A N (A.ρ (pi g) v)=
      (E.sectionRepresentation pi A N).ρ (labelTop pi N hpi (pi g))
        (E.sectionProjection pi A N v)
    rw [labelTop_apply]
    exact Representation.IntertwiningMap.isIntertwining _ _ (E.sectionProjection pi A N) g v

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
  [MulAction Q I] [FaithfulSMul Q I]
  (raw : CliffordRawRestriction.Input) (S : ActualWreathCompressionState Q I)
  {D' : Type} [Group D'] [Finite D']
  (phi : S.D →* D') (hphi : Function.Surjective phi)
  (C : ElementaryMinimalNormalChart phi.ker)

include raw in
theorem actual_retained_constituent_faithful
    (hirr : Representation.IsIrreducible (localRepresentation S phi hphi C).ρ)
    (hfaithful : Function.Injective (localRepresentation S phi hphi C).ρ)
    (N : Subgroup S.A) [N.Normal]
    (W : Subrepresentation (sectionTopRepresentation S phi C N).ρ) (hW : W≠⊥) :
    Function.Injective (constituentLinearKernelRepresentation S phi C N W).ρ := by
  let pi := ActualWreathAffineCapacity.pi S phi
  let A := (ActualWreathAffineCapacity.E S phi C).quotientRepresentation
  let E := ActualWreathAffineCapacity.originalChart S phi C
  let top := labelTop pi N (QuotientGroup.mk'_surjective (elementaryKernel S phi))
  let q0 := primeSectionProjectionOnBase pi A E N
    (QuotientGroup.mk'_surjective (elementaryKernel S phi))
  let tau : Representation (ZMod C.p) (quotientGroup S phi) W.toSubmodule :=
    W.toRepresentation.comp top
  let P : Subrepresentation A.ρ :=
    { toSubmodule := W.toSubmodule.comap q0.toLinearMap
      apply_mem_toSubmodule := by
        intro g v hv
        change q0 (A.ρ g v)∈W
        rw [Representation.IntertwiningMap.isIntertwining]
        exact W.apply_mem_toSubmodule (top g) hv }
  let incl : Representation.IntertwiningMap P.toRepresentation A.ρ :=
    { toLinearMap := P.toSubmodule.subtype
      isIntertwining' _ := rfl }
  let q : Representation.IntertwiningMap P.toRepresentation tau :=
    { toLinearMap :=
        (q0.toLinearMap.comp P.toSubmodule.subtype).codRestrict W.toSubmodule
          (fun v => v.property)
      isIntertwining' g := by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        exact Representation.IntertwiningMap.isIntertwining _ _ q0 g v.val }
  have hq : Function.Surjective q := by
    intro w
    obtain ⟨v,hv⟩ := E.sectionProjection_surjective pi A N w.val
    refine ⟨⟨v,?_⟩,Subtype.ext hv⟩
    change E.sectionProjection pi A N v∈W
    rw [hv]
    exact w.property
  have hWsub : W.toSubmodule≠⊥ := by
    intro hb
    apply hW
    apply Subrepresentation.toSubmodule_injective
    exact hb
  letI : Nontrivial W.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hWsub
  let j := (elementaryCoordinateEmbedding S phi hphi C).comp incl
  have hj : Function.Injective j :=
    (elementaryCoordinateEmbedding_injective S phi hphi C).comp Subtype.val_injective
  let S' := S.quotient D' phi hphi
  letI : MulAction.IsPretransitive Q I := S.top_pretransitive
  letI : FiniteDimensional (ZMod C.p) (localRepresentation S phi hphi C) := by
    change FiniteDimensional (ZMod C.p) C.V
    infer_instance
  have hf := wreath_kernel_subquotient_faithful raw S'.rho S'.rho_injective
    S'.top_surjective S'.fullComponent (localRepresentation S phi hphi C).ρ
    hirr hfaithful P.toRepresentation tau j hj q hq
  exact hf

end SymmetricSubgroupAsymptotics.CliffordHomogeneousRestriction

namespace SymmetricSubgroupAsymptotics.CliffordRawRestriction

/-- The final literature boundary is the raw restriction theorem. The
actual-wreath corollary is constructed, not renamed as a published input. -/
def Input.toHomogeneousRestriction (raw : Input) : CliffordHomogeneousRestriction.Input where
  faithfulNonzeroConstituent := by
    intro Q I _ _ _ _ _ S D' _ _ phi hphi C hirr hfaithful _hcoordinate N _ _hretained W hW
    exact CliffordHomogeneousRestriction.actual_retained_constituent_faithful
      raw S phi hphi C hirr hfaithful N W hW

end SymmetricSubgroupAsymptotics.CliffordRawRestriction
