import SymmetricSubgroupAsymptotics.AffineZeroStabilizer
import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate

/-! Actual point stabilizers in a literal relabelled affine image, and
faithful transport of a displayed linear generating family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AffineModel

variable {p d : ℕ} [Fact p.Prime] {X : Type}

def relabelledAffineMap (R : Subgroup (GLV p d)) (points : V p d ≃ X) :
    Aff R →* Equiv.Perm X :=
  points.permCongrHom.toMonoidHom.comp (action R)

theorem relabelledAffineMap_injective (R : Subgroup (GLV p d)) (points : V p d ≃ X) :
    Function.Injective (relabelledAffineMap R points) :=
  points.permCongrHom.injective.comp (action_injective R)

def literalPointStabilizerEquiv
    (R : Subgroup (GLV p d)) (points : V p d ≃ X)
    (T : Subgroup (Equiv.Perm X)) (hrange : (relabelledAffineMap R points).range=T) :
    MulAction.stabilizer T (points 0) ≃* R := by
  let e : Aff R ≃* T := (MonoidHom.ofInjective
    (relabelledAffineMap_injective R points)).trans (MulEquiv.subgroupCongr hrange)
  apply pointStabilizerEquiv R T e.symm points
  intro g v
  have he : relabelledAffineMap R points (e.symm g)=g.val := by
    exact congrArg Subtype.val (e.apply_symm_apply g)
  have hp := congrArg (fun t : Equiv.Perm X => t (points v)) he
  change points ((action R) (e.symm g) (points.symm (points v)))=g.val (points v) at hp
  simpa only [Equiv.symm_apply_apply] using hp

/-- The image of a literal generated linear group is the literal generated
permutation group when the displayed generators agree pointwise. -/
def generatedLinearImageEquiv
    {I : Type} (g : I → GLV p d) (f : GLV p d →* Equiv.Perm X)
    (hf : Function.Injective f) (h : I → Equiv.Perm X)
    (hgen : ∀ i,f (g i)=h i) :
    Subgroup.closure (Set.range g) ≃* Subgroup.closure (Set.range h) := by
  have he : (Subgroup.closure (Set.range g)).map f=Subgroup.closure (Set.range h) := by
    rw [MonoidHom.map_closure,←Set.range_comp]
    have hh : f ∘ g=h := funext hgen
    rw [hh]
  exact (Subgroup.equivMapOfInjective (Subgroup.closure (Set.range g)) f hf).trans
    (MulEquiv.subgroupCongr he)

end SymmetricSubgroupAsymptotics.AffineModel
