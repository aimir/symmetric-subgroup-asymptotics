import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTensorOddFrames
import SymmetricSubgroupAsymptotics.PrimeRelativeHeadNormalGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow8AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow10AffineSocles

/-! The same original ternary tensor rotations belong to primitive
rows eight and ten. Their four-orbit cover gives head eight regardless
of whether a local ternary quotient exists. This removes the need for
separate exclusion proofs when applying the primitive catalogue. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenOtherTensorFrames

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open BinaryFourAffineImage


def top : Fin 2 → Subgroup (Equiv.Perm (Fin 16)) :=
  ![DegreeTwoPrimitiveSixteenInterfaces.Row8Top, DegreeTwoPrimitiveSixteenInterfaces.Row10Top]

abbrev Rotations := PrimitiveAffineSixteenTensorOddFrames.Rotations
abbrev rotation := PrimitiveAffineSixteenTensorOddFrames.rotation

theorem rotation_mem (j : Fin 2) (m : Rotations) : rotation m ∈ top j := by
  have hgen (k : Fin 2) : DegreeTwoPrimitiveSixteenInterfaces.row4Generators k.castSucc.castSucc ∈ top j := by
    fin_cases j
    · have he : DegreeTwoPrimitiveSixteenInterfaces.row4Generators k.castSucc.castSucc =
          DegreeTwoPrimitiveSixteenInterfaces.row8Generators k.castSucc.castSucc := by
        apply Equiv.ext
        intro x
        revert k x
        decide +kernel
      rw [he]
      exact Subgroup.subset_closure (Set.mem_range_self _)
    · have he : DegreeTwoPrimitiveSixteenInterfaces.row4Generators k.castSucc.castSucc =
          DegreeTwoPrimitiveSixteenInterfaces.row10Generators k.castSucc.castSucc.castSucc := by
        apply Equiv.ext
        intro x
        revert k x
        decide +kernel
      rw [he]
      exact Subgroup.subset_closure (Set.mem_range_self _)
  have ha : DegreeTwoPrimitiveSixteenInterfaces.row4Generators 0 ∈ top j := hgen 0
  have hb : DegreeTwoPrimitiveSixteenInterfaces.row4Generators 1 ∈ top j := hgen 1
  exact (top j).mul_mem ((top j).pow_mem ha _) ((top j).pow_mem hb _)

def rotationToTop (j : Fin 2) : Rotations →* top j where
  toFun m := ⟨rotation m, rotation_mem j m⟩
  map_one' := Subtype.ext rotation.map_one
  map_mul' m n := Subtype.ext (rotation.map_mul m n)

abbrev representatives := PrimitiveAffineSixteenTensorOddFrames.representatives

theorem point_cover : ∀ x : Fin 16,
    ∃ i : Fin 4, ∃ m : Rotations, rotation m (representatives i) = x :=
  PrimitiveAffineSixteenTensorOddFrames.point_cover

theorem odd_image (j : Fin 2) : ¬ 2 ∣ Nat.card (rotationToTop j).range := by
  have hdiv := Subgroup.card_range_dvd (rotationToTop j)
  rw [PrimitiveAffineSixteenTensorOddFrames.rotations_card] at hdiv
  exact fun h => (by decide : ¬ 2 ∣ 9) (h.trans hdiv)

theorem translations_mem (j : Fin 2) (v : Multiplicative Vector) :
    translationPerm v ∈ top j := by
  fin_cases j
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow8AffineSocles.translation_mem v
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow10AffineSocles.translation_mem v

instance top_pretransitive (j : Fin 2) : MulAction.IsPretransitive (top j) (Fin 16) := by
  constructor
  intro x y
  let v : Multiplicative Vector :=
    Multiplicative.ofAdd (pointEquiv.symm y - pointEquiv.symm x)
  refine ⟨⟨translationPerm v, translations_mem j v⟩, ?_⟩
  change pointEquiv ((pointEquiv.symm y - pointEquiv.symm x) + pointEquiv.symm x) = y
  rw [sub_add_cancel, pointEquiv.apply_symm_apply]

theorem normal_generating_pairs (j : Fin 2) :
    ∀ N : Subgroup (top j), N.Normal →
      ∃ z : Fin 2 → top j, Subgroup.normalClosure (Set.range z) = N := by
  fin_cases j
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow8AffineSocles.top_normal_generating_pairs
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow10AffineSocles.top_normal_generating_pairs

theorem original_head_le_eight (j : Fin 2)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (x : Fin 16) (rho : Representation (ZMod 2) (MulAction.stabilizer (top j) x) V)
    (hdim : Module.finrank (ZMod 2) V = 2)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer (top j) x).subtype rho)) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) (top j) (ZMod 2))) ≤ 8 := by
  let A := (rotationToTop j).range
  have hunit : IsUnit (Nat.card A : ZMod 2) :=
    isUnit_iff_ne_zero.mpr ((ZMod.natCast_eq_zero_iff (Nat.card A) 2).not.mpr (odd_image j))
  have hcover : ∀ z : Fin 16, ∃ i : Fin 4, z ∈ MulAction.orbit A (representatives i) := by
    intro z
    obtain ⟨i, m, hm⟩ := point_cover z
    exact ⟨i, MulAction.mem_orbit_iff.mpr ⟨(rotationToTop j).rangeRestrict m, hm⟩⟩
  simpa only [hdim, Nat.reduceMul] using
    CoinducedOddPointOrbitCover.head_le_of_point_cover x A hunit representatives hcover rho B

theorem original_frame_sum_le_ten (j : Fin 2)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (x : Fin 16) (rho : Representation (ZMod 2) (MulAction.stabilizer (top j) x) V)
    (hdim : Module.finrank (ZMod 2) V = 2)
    (N : Subgroup (top j)) [N.Normal]
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer (top j) x).subtype rho)) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) +
      Module.finrank (ZMod 2)
        (B.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod 2) (top j) (ZMod 2))) ≤ 10 := by
  obtain ⟨z, hz⟩ := normal_generating_pairs j N inferInstance
  have hn := primeRelativeHead_le_normal_generating_tuple 2 N z hz
  have hb := original_head_le_eight j x rho hdim B
  omega

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenOtherTensorFrames

end
