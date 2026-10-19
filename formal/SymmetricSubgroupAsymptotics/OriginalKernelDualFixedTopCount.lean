import SymmetricSubgroupAsymptotics.RepresentationDualComp
import SymmetricSubgroupAsymptotics.EquivariantBinaryRestrictionCount
import SymmetricSubgroupAsymptotics.Non2LiftBound
import SymmetricSubgroupAsymptotics.SurjectiveRepresentationGeneratorTransport

/-! Fixed-top lift counting from actual dual generators of the original kernel.
Section values are retained, so no multiplicity of top maps is discarded. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalKernelDualFixedTopCount

variable {Q T J : Type} [Group Q] [Group T] [Group J]
    (pi : Q →* T) (A : Rep.{0} (ZMod 2) T)
    (E : OriginalKernelModuleChart pi A) (theta : J →* T)

abbrev Lift := {phi : J →* Q // pi.comp phi = theta}

def restriction (phi : Lift pi theta) :
    EquivariantBinaryRestrictionCount.Restriction theta.ker (A.ρ.comp theta) where
  hom := ((E.equiv.symm.toMonoidHom).comp
    ((phi.val.comp theta.ker.subtype).codRestrict pi.ker (by
      intro x
      have h := DFunLike.congr_fun phi.property (x : J)
      exact h.trans x.property))).toAdditiveLeft
  equivariant g x := by
    apply E.equiv.injective
    apply Subtype.ext
    simp only [MonoidHom.coe_toAdditiveLeft, Function.comp_apply,
      MonoidHom.comp_apply]
    change (E.equiv (E.equiv.symm ⟨phi.val (g * (x : J) * g⁻¹), _⟩) : Q) =
      (E.equiv (Multiplicative.ofAdd
        (A.ρ (theta g) (Multiplicative.toAdd
          (E.equiv.symm ⟨phi.val (x : J), _⟩)))) : Q)
    rw [E.equiv.apply_symm_apply]
    have hg := DFunLike.congr_fun phi.property g
    change pi (phi.val g) = theta g at hg
    rw [← hg, E.conjugate]
    simp only [map_mul, map_inv, ofAdd_toAdd,
      MulEquiv.apply_symm_apply]

include E in
theorem fixed_top_card_le [Finite Q] [Finite T] [Finite J]
    (htheta : Function.Surjective theta) {H : ℕ}
    (hgen : RepresentationGeneratedBy A.ρ.dual H) :
    Nat.card (Lift pi theta) ≤
      Nat.card Q ^ Nat.card T * 2 ^ (H * binaryCharacterRank theta.ker) := by
  have hthetaSaved := htheta
  choose s hs using htheta
  let encoding : Lift pi theta → (T → Q) ×
      EquivariantBinaryRestrictionCount.Restriction theta.ker (A.ρ.comp theta) :=
    fun phi => (fun t => phi.val (s t), restriction pi A E theta phi)
  have hi : Function.Injective encoding := by
    intro phi chi h
    apply Subtype.ext
    apply MonoidHom.ext
    intro g
    let t := theta g
    have hm : (s t)⁻¹ * g ∈ theta.ker := by
      change theta ((s t)⁻¹ * g) = 1
      rw [map_mul, map_inv, hs]
      exact inv_mul_cancel t
    have hr := congrArg
      (fun e => e.2.hom (Additive.ofMul (⟨(s t)⁻¹*g, hm⟩ : theta.ker))) h
    have hf := congrArg (fun v : A =>
      (E.equiv (Multiplicative.ofAdd v) : Q)) hr
    simp [encoding, restriction, MonoidHom.coe_toAdditiveLeft] at hf
    have hv := congrArg (fun e => e.1 t) h
    change phi.val (s t) = chi.val (s t) at hv
    rw [hv] at hf
    exact mul_left_cancel hf
  have hdual : RepresentationGeneratedBy (Representation.dual (A.ρ.comp theta)) H := by
    rw [representation_dual_comp]
    exact representationGeneratedBy_comp_of_surjective A.ρ.dual theta hthetaSaved hgen
  have hc := EquivariantBinaryRestrictionCount.card_le theta.ker
    (A.ρ.comp theta) hdual
  letI := representationGenerated_intertwiner_finite (Representation.dual (A.ρ.comp theta))
    (DerivedHead.conjRep 2 J theta.ker) hdual
  letI : Finite (EquivariantBinaryRestrictionCount.Restriction theta.ker
      (A.ρ.comp theta)) := Finite.of_injective
    (EquivariantBinaryRestrictionCount.encode theta.ker (A.ρ.comp theta))
    (EquivariantBinaryRestrictionCount.encode_injective theta.ker (A.ρ.comp theta))
  have hh := Nat.card_le_card_of_injective encoding hi
  rw [Nat.card_prod, Nat.card_fun] at hh
  exact hh.trans (Nat.mul_le_mul_left _ hc)

end SymmetricSubgroupAsymptotics.OriginalKernelDualFixedTopCount
