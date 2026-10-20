import SymmetricSubgroupAsymptotics.CoinducedOddPointOrbitCover
import SymmetricSubgroupAsymptotics.PrimeRelativeHeadNormalGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow4AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow7AffineSocles

/-! The two remaining eligible primitive-sixteen literals share the
actual ternary tensor rotations. Their odd C3 by C3 image has four
physical point orbits: zero, rank-one matrices, and the two invertible
matrix orbits. Averaging gives head eight for every local binary plane;
the checked original all-normal width two gives the required total ten. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTensorOddFrames

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open BinaryFourAffineImage
open PrimitiveAffineDegreeTwoPrimitiveSixteenRows4And7LinearRelations

def top : Fin 2 → Subgroup (Equiv.Perm (Fin 16)) :=
  ![DegreeTwoPrimitiveSixteenInterfaces.Row4Top, DegreeTwoPrimitiveSixteenInterfaces.Row7Top]

abbrev Rotations := Multiplicative (ZMod 3) × Multiplicative (ZMod 3)

def rotation : Rotations →* Equiv.Perm (Fin 16) where
  toFun m := (DegreeTwoPrimitiveSixteenInterfaces.row4Generators 0) ^ m.1.toAdd.val *
    (DegreeTwoPrimitiveSixteenInterfaces.row4Generators 1) ^ m.2.toAdd.val
  map_one' := rfl
  map_mul' m n := by
    apply Equiv.ext
    intro x
    revert m n x
    decide +kernel

theorem rotation_mem (j : Fin 2) (m : Rotations) : rotation m ∈ top j := by
  have ha : DegreeTwoPrimitiveSixteenInterfaces.row4Generators 0 ∈ top j := by
    fin_cases j
    · exact Subgroup.subset_closure (Set.mem_range_self 0)
    · rw [← a4_original, a7_original]
      exact Subgroup.subset_closure (Set.mem_range_self 0)
  have hb : DegreeTwoPrimitiveSixteenInterfaces.row4Generators 1 ∈ top j := by
    fin_cases j
    · exact Subgroup.subset_closure (Set.mem_range_self 1)
    · rw [← b4_original, b7_original]
      exact Subgroup.subset_closure (Set.mem_range_self 1)
  exact (top j).mul_mem ((top j).pow_mem ha _) ((top j).pow_mem hb _)

def rotationToTop (j : Fin 2) : Rotations →* top j where
  toFun m := ⟨rotation m, rotation_mem j m⟩
  map_one' := Subtype.ext rotation.map_one
  map_mul' m n := Subtype.ext (rotation.map_mul m n)

def representatives : Fin 4 → Fin 16 := ![0, 1, 9, 6]

/-- The finite check concerns only the fixed nine rotation parameters and
sixteen physical points. It does not enumerate either ambient group. -/
theorem point_cover : ∀ x : Fin 16,
    ∃ i : Fin 4, ∃ m : Rotations, rotation m (representatives i) = x := by
  decide +kernel

theorem rotations_card : Nat.card Rotations = 9 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem odd_image (j : Fin 2) : ¬ 2 ∣ Nat.card (rotationToTop j).range := by
  have hdiv := Subgroup.card_range_dvd (rotationToTop j)
  rw [rotations_card] at hdiv
  exact fun h => (by decide : ¬ 2 ∣ 9) (h.trans hdiv)

theorem translations_mem (j : Fin 2) (v : Multiplicative Vector) :
    translationPerm v ∈ top j := by
  fin_cases j
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow4AffineSocles.translation_mem v
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow7AffineSocles.translation_mem v

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
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow4AffineSocles.top_normal_generating_pairs
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow7AffineSocles.top_normal_generating_pairs

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

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTensorOddFrames

end
