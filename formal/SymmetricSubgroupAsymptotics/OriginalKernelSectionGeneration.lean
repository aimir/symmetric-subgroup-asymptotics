import SymmetricSubgroupAsymptotics.OriginalKernelArbitraryNormalQuotient
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators
import SymmetricSubgroupAsymptotics.RepresentationGeneratorExtension

/-! Generator tuples descend to the exact kernel section of an arbitrary
original normal quotient. The acting group is the original G throughout
the projection, then its actual residual quotient; no splitting is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart

variable {p : ℕ} {G B : Type} [Group G] [Group B]
  (pi : G →* B) (A : Rep (ZMod p) B) (E : OriginalKernelModuleChart pi A)
  (N : Subgroup G) [N.Normal]

private theorem sectionMap_equiv (a : A) :
    (E.sectionMap pi A N (E.equiv (Multiplicative.ofAdd a))).toAdd=
      (normalSpace pi A E N).mkQ a := by
  change (normalSpace pi A E N).mkQ
    (E.equiv.symm (E.equiv (Multiplicative.ofAdd a))).toAdd=_
  simp only [E.equiv.symm_apply_apply,toAdd_ofAdd]

def sectionProjection :
    Representation.IntertwiningMap (A.ρ.comp pi)
      ((E.sectionRepresentation pi A N).ρ.comp
        (QuotientGroup.mk' (pi.ker ⊔ N))) where
  toLinearMap := (normalSpace pi A E N).mkQ
  isIntertwining' g := by
    apply LinearMap.ext
    intro a
    have h := E.sectionRepresentation_apply pi A N g (E.equiv (Multiplicative.ofAdd a))
    have hk : MulAut.conjNormal g (E.equiv (Multiplicative.ofAdd a))=
        E.equiv (Multiplicative.ofAdd (A.ρ (pi g) a)) := by
      apply Subtype.ext
      exact (E.conjugate g a).symm
    rw [hk,E.sectionMap_equiv,E.sectionMap_equiv] at h
    change (normalSpace pi A E N).mkQ (A.ρ (pi g) a)=
      (E.sectionRepresentation pi A N).ρ (QuotientGroup.mk' (pi.ker ⊔ N) g)
        ((normalSpace pi A E N).mkQ a)
    exact h.symm

theorem sectionProjection_surjective : Function.Surjective (E.sectionProjection pi A N) :=
  (normalSpace pi A E N).mkQ_surjective

/-- The tuple still generates with the original G-action pulled back from
its actual residual top. This is the input for finite-image dimension. -/
theorem sectionGeneratedBy [Fact p.Prime] {r : ℕ} (hpi : Function.Surjective pi)
    (hgen : RepresentationGeneratedBy A.ρ r) :
    RepresentationGeneratedBy
      ((show Representation (ZMod p) (G ⧸ (pi.ker ⊔ N))
          (E.sectionModule pi A N) from (E.sectionRepresentation pi A N).ρ).comp
        (QuotientGroup.mk' (pi.ker ⊔ N))) r := by
  let rho : Representation (ZMod p) G A := A.ρ.comp pi
  let sigma : Representation (ZMod p) G (E.sectionModule pi A N) :=
    (E.sectionRepresentation pi A N).ρ.comp (QuotientGroup.mk' (pi.ker ⊔ N))
  have hsource : RepresentationGeneratedBy rho r :=
    RepresentationGeneratedBy.comp_of_surjective A.ρ pi hpi hgen
  obtain ⟨v,hv⟩ := hsource
  let F : rho.asModule →ₗ[(ZMod p)[G]] sigma.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule rho sigma
      (E.sectionProjection pi A N)
  have hsurj : Function.Surjective F := by
    intro y
    obtain ⟨x,hx⟩ := E.sectionProjection_surjective pi A N y
    exact ⟨x,hx⟩
  refine ⟨fun i => F (v i),?_⟩
  have hm := congrArg (Submodule.map F) hv
  rw [Submodule.map_top,LinearMap.range_eq_top.mpr hsurj,Submodule.map_span] at hm
  rw [← Set.range_comp] at hm
  simpa only [Function.comp_def] using hm

end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
