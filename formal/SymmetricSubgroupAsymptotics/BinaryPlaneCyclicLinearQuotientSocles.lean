import SymmetricSubgroupAsymptotics.BinaryPlaneWreathNormalGenerators
import SymmetricSubgroupAsymptotics.TernaryPermutationWreathCyclicQuotientSocles

/-! Every actual cyclic-top binary-plane LINEAR image has quotient-socle
bound two. This does not assert all-normal subgroup inheritance. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPlaneCyclicLinearQuotientSocles
open BinaryPlaneWreathIrreducible BinaryPlaneWreathNormalGenerators

variable {R I Q : Type} [Group R] [Finite R] [IsCyclic R]
  [MulAction R I] [Fintype I] [DecidableEq I] [Group Q]

 theorem socle_of_surjective (C : Subgroup (W (R := R) (I := I)))
    (hsurj : Function.Surjective
      ((PermutationalWreathProduct.rightHom : W (R := R) (I := I) →* R).comp C.subtype))
    (c : R) (i : I) (hcycle : ∀ j : I, ∃ n : ℕ, c^n • i=j)
    (hR : Nat.Coprime 3 (Nat.card R))
    (pi : C →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q 2 := by
  let f := (wreathMap (R := R) (I := I)).comp C.subtype
  let J := f.range
  let e : C ≃* J := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun _ _ h => (wreathMap_injective.comp Subtype.val_injective)
      (congrArg Subtype.val h),f.rangeRestrict_surjective⟩
  have hb : Function.Surjective
      ((PermutationalWreathProduct.rightHom :
        TernaryPermutationWreathEmbedding.W (R := R) (I := I) →* R).comp J.subtype) := by
    intro r
    obtain ⟨g,hg⟩ := hsurj r
    exact ⟨f.rangeRestrict g,hg⟩
  exact TernaryPermutationWreathCyclicQuotientSocles.socle_of_surjective
    J hb c i hcycle hR (pi.comp e.symm.toMonoidHom) (hpi.comp e.symm.surjective)

end SymmetricSubgroupAsymptotics.BinaryPlaneCyclicLinearQuotientSocles
