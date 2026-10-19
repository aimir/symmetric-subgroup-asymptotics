import SymmetricSubgroupAsymptotics.RepresentationGeneratedIntertwinerCount
import SymmetricSubgroupAsymptotics.Non2PreE7DerivedHeadCount
import SymmetricSubgroupAsymptotics.BinaryAbelianization

/-! An actual equivariant restriction is encoded by pullback of its dual.
No choice of a replacement elementary quotient or split extension occurs. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.EquivariantBinaryRestrictionCount

variable {J V : Type} [Group J] [AddCommGroup V] [Module (ZMod 2) V]
    (F : Subgroup J) [F.Normal] (rho : Representation (ZMod 2) J V)

/-- The conjugacy condition is on the original subgroup and original map. -/
structure Restriction where
  hom : Additive F →+ V
  equivariant : ∀ (g : J) (x : F),
    hom (Additive.ofMul (MulAut.conjNormal g x)) =
      rho g (hom (Additive.ofMul x))

/-- Pullback of literal binary linear forms. -/
def encode (r : Restriction F rho) :
    rho.dual.IntertwiningMap (DerivedHead.conjRep 2 J F) where
  toLinearMap := primeCharacterPullback 2 F r.hom
  isIntertwining' g := by
    apply LinearMap.ext
    intro ell
    apply AddMonoidHom.ext
    intro x
    change ell (rho g⁻¹ (r.hom x)) =
      ell (r.hom (Additive.ofMul (MulAut.conjNormal g⁻¹ (Additive.toMul x))))
    exact congrArg ell (r.equivariant g⁻¹ (Additive.toMul x)).symm

/-- All dual forms separate the original values, including zero restrictions. -/
theorem encode_injective : Function.Injective (encode F rho) := by
  intro r s h
  have hh : r.hom = s.hom := by
    apply AddMonoidHom.ext
    intro x
    apply sub_eq_zero.mp
    apply (Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).mp
    intro ell
    have he := congrArg (fun f : rho.dual.IntertwiningMap
      (DerivedHead.conjRep 2 J F) => f ell x) h
    change ell (r.hom x) = ell (s.hom x) at he
    simpa only [map_sub, sub_eq_zero] using he
  cases r
  cases s
  cases hh
  rfl

/-- H generators of the actual dual cost H original binary characters. -/
theorem card_le [Finite F] {H : ℕ}
    (hgen : RepresentationGeneratedBy rho.dual H) :
    Nat.card (Restriction F rho) ≤ 2 ^ (H * binaryCharacterRank F) := by
  letI := representationGenerated_intertwiner_finite rho.dual
    (DerivedHead.conjRep 2 J F) hgen
  have h := (Nat.card_le_card_of_injective (encode F rho)
    (encode_injective F rho)).trans
    (representationGenerated_intertwiner_card_le rho.dual
      (DerivedHead.conjRep 2 J F) hgen)
  have hc : Nat.card (PrimeCharacters 2 F) = 2 ^ binaryCharacterRank F := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    rfl
  rw [hc, ← pow_mul] at h
  simpa only [Nat.mul_comm] using h

end SymmetricSubgroupAsymptotics.EquivariantBinaryRestrictionCount
