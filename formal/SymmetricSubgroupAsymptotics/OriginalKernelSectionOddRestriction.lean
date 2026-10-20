import SymmetricSubgroupAsymptotics.OriginalKernelSectionGeneration
import SymmetricSubgroupAsymptotics.RepresentationFixedFreeQuotient
import SymmetricSubgroupAsymptotics.CyclicSocleQuotientTools

/-! The exact original kernel section may be restricted to an odd subgroup
of the original acting image. Averaging is never applied to the full even
extension or to its odd-subgroup preimage. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart

variable {G B : Type} [Group G] [Group B]
  (pi : G →* B) (A : Rep.{0} (ZMod 2) B) (E : OriginalKernelModuleChart pi A)
  (N : Subgroup G) [N.Normal]

/-- Canonical map from the original acting image to the literal residual
acting quotient, rather than an isomorphism-class replacement. -/
def sectionTop (hpi : Function.Surjective pi) : B →* G ⧸ (pi.ker ⊔ N) :=
  pi.liftOfSurjective hpi ⟨QuotientGroup.mk' (pi.ker ⊔ N),by
    rw [QuotientGroup.ker_mk']
    exact le_sup_left⟩

theorem sectionTop_comp (hpi : Function.Surjective pi) :
    (sectionTop pi N hpi).comp pi=QuotientGroup.mk' (pi.ker ⊔ N) :=
  pi.liftOfRightInverse_comp (Function.surjInv hpi)
    (Function.rightInverse_surjInv hpi) _

@[simp] theorem sectionTop_apply (hpi : Function.Surjective pi) (g : G) :
    sectionTop pi N hpi (pi g)=QuotientGroup.mk' (pi.ker ⊔ N) g :=
  DFunLike.congr_fun (sectionTop_comp pi N hpi) g

/-- The actual section projection is equivariant for the original image B,
not only for the original extension G. -/
def sectionProjectionOnBase (hpi : Function.Surjective pi) :
    Representation.IntertwiningMap A.ρ
      ((E.sectionRepresentation pi A N).ρ.comp (sectionTop pi N hpi)) where
  toLinearMap := (E.sectionProjection pi A N).toLinearMap
  isIntertwining' b := by
    apply LinearMap.ext
    intro a
    obtain ⟨g,rfl⟩ := hpi b
    change (E.sectionProjection pi A N) (A.ρ (pi g) a)=
      (E.sectionRepresentation pi A N).ρ (sectionTop pi N hpi (pi g))
        ((E.sectionProjection pi A N) a)
    rw [sectionTop_apply]
    exact Representation.IntertwiningMap.isIntertwining _ _
      (E.sectionProjection pi A N) g a

theorem sectionProjectionOnBase_surjective (hpi : Function.Surjective pi) :
    Function.Surjective (E.sectionProjectionOnBase pi A N hpi) :=
  E.sectionProjection_surjective pi A N

/-- No fixed vectors survive in the arbitrary original kernel section
under a finite subgroup of invertible order. -/
theorem sectionFixedFreeOnOdd (hpi : Function.Surjective pi)
    (O : Subgroup B) [Finite O] [NeZero (Nat.card O : ZMod 2)]
    (hfixed : ∀ a : A, (∀ o : O, A.ρ (o : B) a=a) → a=0) :
    ∀ v : E.sectionModule pi A N,
      (∀ o : O, (E.sectionRepresentation pi A N).ρ
        (sectionTop pi N hpi (o : B)) v=v) → v=0 := by
  let sigma : Representation (ZMod 2) O (E.sectionModule pi A N) :=
    (E.sectionRepresentation pi A N).ρ.comp ((sectionTop pi N hpi).comp O.subtype)
  let q : Representation.IntertwiningMap (A.ρ.comp O.subtype) sigma :=
    { toLinearMap := (E.sectionProjectionOnBase pi A N hpi).toLinearMap
      isIntertwining' o := by
        apply LinearMap.ext
        intro a
        exact Representation.IntertwiningMap.isIntertwining _ _
          (E.sectionProjectionOnBase pi A N hpi) (o : B) a }
  exact RepresentationFixedFreeQuotient.of_surjective (A.ρ.comp O.subtype) sigma q
    (E.sectionProjectionOnBase_surjective pi A N hpi) hfixed

end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
