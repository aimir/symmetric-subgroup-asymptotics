import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0TopCertificate
import SymmetricSubgroupAsymptotics.CoinducedTwoOrbitNormalizerHead
import SymmetricSubgroupAsymptotics.BinaryPlaneTernaryInvariants
import SymmetricSubgroupAsymptotics.CoinducedGroupLocalTransport

/-! A small original-frame certificate for historical top1/frame0.
The actual point stabilizer has order three. Its simultaneous action with
the central block swap has one killed orbit and one free orbit on the
eight cosets. The resulting local-plane evaluation bound replaces the
historical module and submodule registries, preserving every local epi
and faithful binary-plane representation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop1NormalizerHead

abbrev Source := PrimitiveAffineEightFrameRow0TopCertificate.Source
local instance : Group Source := PrimitiveAffineEightFrameRow0TopCertificate.group

abbrev Literal := Subgroup.closure
  (Set.range PrimitiveAffineEightFrameRow0TopCertificate.generators)
abbrev literalStabilizer := MulAction.stabilizer Literal (0 : Fin 8)

def stabilizer : Subgroup Source := literalStabilizer.comap
  PrimitiveAffineEightFrameRow0TopCertificate.originalEquiv.toMonoidHom

instance stabilizerMembership (x : Source) : Decidable (x ∈ stabilizer) :=
  decidable_of_iff
    (PrimitiveAffineEightFrameRow0TopCertificate.certificate.toCayley.elements x.index 0 = 0)
    (by rfl)

theorem stabilizer_card : Nat.card stabilizer = 3 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

def swap : Source := PrimitiveAffineEightFrameRow0TopCertificate.ambient 3
def movingRepresentative : Source := PrimitiveAffineEightFrameRow0TopCertificate.ambient 2

theorem swap_normalizes : swap ∈ Subgroup.normalizer (stabilizer : Set Source) := by
  change ∀ x : Source, x ∈ stabilizer ↔ swap * x * swap⁻¹ ∈ stabilizer
  decide +kernel

/-- Only the retained twenty-four original rows are checked here. The
four shapes use the original stabilizer and the two literal generators. -/
theorem twoOrbitCover :
    CoinducedTwoOrbitNormalizerHead.Cover stabilizer swap movingRepresentative := by
  unfold CoinducedTwoOrbitNormalizerHead.Cover
  decide +kernel

def stabilizerEquiv : stabilizer ≃* literalStabilizer where
  toFun h := ⟨PrimitiveAffineEightFrameRow0TopCertificate.originalEquiv h.1, h.2⟩
  invFun h := ⟨PrimitiveAffineEightFrameRow0TopCertificate.originalEquiv.symm h.1, by
    change PrimitiveAffineEightFrameRow0TopCertificate.originalEquiv
      (PrimitiveAffineEightFrameRow0TopCertificate.originalEquiv.symm h.1) ∈ literalStabilizer
    rw [MulEquiv.apply_symm_apply]
    exact h.2⟩
  left_inv h := Subtype.ext
    (PrimitiveAffineEightFrameRow0TopCertificate.originalEquiv.symm_apply_apply h.1)
  right_inv h := Subtype.ext
    (PrimitiveAffineEightFrameRow0TopCertificate.originalEquiv.apply_symm_apply h.1)
  map_mul' h k := Subtype.ext
    (PrimitiveAffineEightFrameRow0TopCertificate.originalEquiv.map_mul h.1 k.1)

theorem source_head_le_two {L V : Type} [Group L] [Finite L]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (f : stabilizer →* L) (hf : Function.Surjective f)
    (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (rho : Representation (ZMod 2) L V)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation (Representation.coind stabilizer.subtype (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) Source (ZMod 2))) ≤ 2 := by
  have hcard : Nat.card L ≤ 3 := by
    simpa only [stabilizer_card] using Nat.card_le_card_of_surjective f hf
  have hthree : Nat.card L = 3 := by omega
  have hz := BinaryPlaneTernaryInvariants.invariants_eq_bot_of_card_three
    rho hthree hdim hrho
  have hzero : Representation.invariants (rho.comp f) = ⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    have hvL : v ∈ Representation.invariants rho := by
      intro l
      obtain ⟨h, rfl⟩ := hf l
      exact hv h
    rw [hz] at hvL
    exact hvL
  have hunit : IsUnit (Nat.card stabilizer : ZMod 2) := by
    have hthreeMod : (3 : ZMod 2) = 1 := by decide
    rw [stabilizer_card]
    change IsUnit (3 : ZMod 2)
    rw [hthreeMod]
    exact isUnit_one
  simpa only [hdim] using
    CoinducedTwoOrbitNormalizerHead.subrepresentation_head_le_local_dimension
      stabilizer (rho.comp f) swap movingRepresentative hunit swap_normalizes hzero twoOrbitCover B

/-- The arbitrary original local map is on the literal point stabilizer.
The computational model is used only through the exact commuting maps. -/
theorem literal_head_le_two {L V : Type} [Group L] [Finite L]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (f : literalStabilizer →* L) (hf : Function.Surjective f)
    (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (rho : Representation (ZMod 2) L V)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation (Representation.coind literalStabilizer.subtype (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) Literal (ZMod 2))) ≤ 2 := by
  let eG := PrimitiveAffineEightFrameRow0TopCertificate.originalEquiv.symm
  let f' := f.comp stabilizerEquiv.toMonoidHom
  let eV : Representation.Equiv (rho.comp f)
      ((rho.comp f').comp stabilizerEquiv.symm.toMonoidHom) := {
    toLinearEquiv := LinearEquiv.refl (ZMod 2) V
    isIntertwining' := by
      intro h
      ext v
      change rho (f h) v = rho (f (stabilizerEquiv (stabilizerEquiv.symm h))) v
      rw [stabilizerEquiv.apply_symm_apply] }
  exact CoinducedGroupLocalTransport.uniform_head_le literalStabilizer stabilizer
    eG stabilizerEquiv.symm (fun _ => rfl) (rho.comp f) (rho.comp f') eV 2
    (fun A => source_head_le_two f' (hf.comp stabilizerEquiv.surjective) hL rho hdim hrho A) B

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop1NormalizerHead

end
