import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1TopCertificate
import SymmetricSubgroupAsymptotics.CyclicThreeNormalizerPointCertificate
import SymmetricSubgroupAsymptotics.CoinducedGroupLocalTransport

/-! Selected original top2 point-cover pilot. Its cyclic Sylow generator,
normalizer word and eight physical point words are checked in the retained
24-element source. All local epimorphisms and faithful planes stay arbitrary. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop2NormalizerHead

abbrev Source := PrimitiveAffineEightFrameRow1TopCertificate.Source
local instance : Group Source := PrimitiveAffineEightFrameRow1TopCertificate.group
abbrev Literal := Subgroup.closure
  (Set.range PrimitiveAffineEightFrameRow1TopCertificate.generators)

local instance sourceAction : MulAction Source (Fin 8) :=
  MulAction.compHom (Fin 8) PrimitiveAffineEightFrameRow1TopCertificate.originalEquiv.toMonoidHom

local instance sourceTransitive : MulAction.IsPretransitive Source (Fin 8) := ⟨by
  intro x y
  revert x y
  decide +kernel⟩

def generator : Source := PrimitiveAffineEightFrameRow1TopCertificate.ambient 0
def normalizer : Source := PrimitiveAffineEightFrameRow1TopCertificate.ambient 2 *
  PrimitiveAffineEightFrameRow1TopCertificate.ambient 3

local instance threePrime : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem generator_order : orderOf generator = 3 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem cyclic_membership (x : Source) :
    x ∈ Subgroup.zpowers generator ↔ x = 1 ∨ x = generator ∨ x = generator ^ 2 := by
  rw [mem_zpowers_iff_mem_range_orderOf, generator_order]
  constructor
  · intro hx
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hx
    have ha3 : a < 3 := Finset.mem_range.mp ha
    interval_cases a <;> simp_all
  · rintro (rfl | rfl | rfl)
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by decide), by simp⟩
    · exact Finset.mem_image.mpr ⟨1, Finset.mem_range.mpr (by decide), by simp⟩
    · exact Finset.mem_image.mpr ⟨2, Finset.mem_range.mpr (by decide), rfl⟩

local instance cyclicMembership (x : Source) :
    Decidable (x ∈ Subgroup.zpowers generator) :=
  decidable_of_iff (x = 1 ∨ x = generator ∨ x = generator ^ 2) (cyclic_membership x).symm

theorem normalizes : normalizer ∈
    Subgroup.normalizer (Subgroup.zpowers generator : Set Source) := by
  change ∀ x : Source, x ∈ Subgroup.zpowers generator ↔
    normalizer * x * normalizer⁻¹ ∈ Subgroup.zpowers generator
  decide +kernel

def path : Fin 8 → List (Fin 4) :=
  ![[], [], [1], [0], [2], [], [2, 0], [0, 2]]

def pointCertificate : CyclicThreeNormalizerPointCertificate.Certificate (G := Source) (Fin 8) where
  generator := generator
  generator_order := generator_order
  group_factorization := by
    rw [PrimitiveAffineEightFrameRow1TopCertificate.source_card]
    decide +kernel
  normalizer := normalizer
  normalizes := normalizes
  representative := 1
  path := path
  covers := by decide +kernel

abbrev literalStabilizer := MulAction.stabilizer Literal (0 : Fin 8)
abbrev stabilizer := MulAction.stabilizer Source (0 : Fin 8)

def stabilizerEquiv : stabilizer ≃* literalStabilizer where
  toFun h := ⟨PrimitiveAffineEightFrameRow1TopCertificate.originalEquiv h.1, h.2⟩
  invFun h := ⟨PrimitiveAffineEightFrameRow1TopCertificate.originalEquiv.symm h.1, by
    change PrimitiveAffineEightFrameRow1TopCertificate.originalEquiv
      (PrimitiveAffineEightFrameRow1TopCertificate.originalEquiv.symm h.1) ∈ literalStabilizer
    rw [MulEquiv.apply_symm_apply]
    exact h.2⟩
  left_inv h := Subtype.ext
    (PrimitiveAffineEightFrameRow1TopCertificate.originalEquiv.symm_apply_apply h.1)
  right_inv h := Subtype.ext
    (PrimitiveAffineEightFrameRow1TopCertificate.originalEquiv.apply_symm_apply h.1)
  map_mul' h k := Subtype.ext
    (PrimitiveAffineEightFrameRow1TopCertificate.originalEquiv.map_mul h.1 k.1)

theorem source_head_le_two {L V : Type} [Group L] [Finite L]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (f : stabilizer →* L) (hf : Function.Surjective f)
    (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (rho : Representation (ZMod 2) L V)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation (Representation.coind stabilizer.subtype (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) Source (ZMod 2))) ≤ 2 :=
  pointCertificate.head_le_two 0 f hf rho hL hdim hrho B

theorem literal_head_le_two {L V : Type} [Group L] [Finite L]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (f : literalStabilizer →* L) (hf : Function.Surjective f)
    (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (rho : Representation (ZMod 2) L V)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation (Representation.coind literalStabilizer.subtype (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) Literal (ZMod 2))) ≤ 2 := by
  let eG := PrimitiveAffineEightFrameRow1TopCertificate.originalEquiv.symm
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

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop2NormalizerHead

end
