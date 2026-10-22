import SymmetricSubgroupAsymptotics.CFSGSymplecticOddPointAutomorphisms
import SymmetricSubgroupAsymptotics.CFSGSymplecticCollineationCardinality
import SymmetricSubgroupAsymptotics.CFSGSymplecticCenterCardinality
import SymmetricSubgroupAsymptotics.CFSGOuterCardinalityCancellation

/-! The actual odd-characteristic projective symplectic outer group
has order at most twice the field-automorphism count. Both recognition
and the projective similitude count are proved on the original quotient. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticPointRootLabels
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
open CFSGSymplecticCollineationSimilitudes PrimitiveSocleRawStructure
variable {K : Type} [Field K] [Finite K]

def oddOrthogonalHom (p r : ℕ) [Fact p.Prime] [CharP K p]
    (hr : 0 < r) (htwo : (2 : K) ≠ 0) :
    MulAut (elementaryProjective K (r + 1)) →* orthogonalGroup (K := K) (r + 1) :=
  (oddCollineationHom p r hr htwo).codRestrict _ (fun f =>
    orthogonal_iff_of_label_map r hr f _ (oddPointHom_label p r hr htwo f))

theorem oddOrthogonalHom_injective (p r : ℕ) [Fact p.Prime] [CharP K p]
    (hr : 0 < r) (htwo : (2 : K) ≠ 0)
    [IsSimpleGroup (elementaryProjective K (r + 1))] :
    Function.Injective (oddOrthogonalHom p r hr htwo) := by
  intro f g h
  exact oddCollineationHom_injective p r hr htwo (congrArg Subtype.val h)

theorem projective_noncommutative (r : ℕ) (hr : 0 < r) :
    ¬ IsMulCommutative (elementaryProjective K (r + 1)) := by
  intro hc
  letI := hc
  let v : Index (r + 1) → K := Pi.single (Sum.inl 0) 1
  let w : Index (r + 1) → K := Pi.single (Sum.inr 0) 1
  have h := (projectiveNaturalRootElement_commute_iff r hr v w (1 : K) 1
    one_ne_zero one_ne_zero).mp (show Commute _ _ from hc.is_comm.comm _ _)
  have hh : (1 : K) = 0 := by simpa only [v, w, pairing_neg_basis, Pi.single_eq_same] using h
  exact one_ne_zero hh

theorem odd_automorphism_card_le (p r : ℕ) [Fact p.Prime] [CharP K p]
    (hr : 0 < r) (htwo : (2 : K) ≠ 0)
    [IsSimpleGroup (elementaryProjective K (r + 1))] :
    Nat.card (MulAut (elementaryProjective K (r + 1))) ≤
      Nat.card (elementaryRootGroup K (r + 1)) * Nat.card (K ≃+* K) := by
  let b : Index (r + 1) := Sum.inl 0
  let i : Index (r + 1) := Sum.inl ⟨1, by omega⟩
  let j : Index (r + 1) := Sum.inr 0
  have hbi : b ≠ i := by simp [b, i, Fin.ext_iff]
  have hbj : b ≠ j := by simp [b, j]
  have hij : i ≠ j := by simp [i, j]
  exact (Nat.card_le_card_of_injective _ (oddOrthogonalHom_injective p r hr htwo)).trans
    (orthogonalGroup_card_le (r + 1) (by omega) b i j hbi hbj hij)

theorem odd_outer_card_le (p r : ℕ) [Fact p.Prime] [CharP K p]
    (hr : 0 < r) (htwo : (2 : K) ≠ 0)
    [IsSimpleGroup (elementaryProjective K (r + 1))] :
    Nat.card (Outer (elementaryProjective K (r + 1))) ≤ 2 * Nat.card (K ≃+* K) := by
  have hc := (Subgroup.center (elementaryRootGroup K (r + 1))).card_mul_index
  change Nat.card (Subgroup.center (elementaryRootGroup K (r + 1))) *
    Nat.card (elementaryProjective K (r + 1)) = Nat.card (elementaryRootGroup K (r + 1)) at hc
  apply CFSGOuterCardinalityCancellation.outer_card_le_of_automorphism_bound
    (projective_noncommutative r hr)
  calc
    Nat.card (MulAut (elementaryProjective K (r + 1))) ≤
      Nat.card (elementaryRootGroup K (r + 1)) * Nat.card (K ≃+* K) :=
        odd_automorphism_card_le p r hr htwo
    _ = (Nat.card (Subgroup.center (elementaryRootGroup K (r + 1))) *
      Nat.card (elementaryProjective K (r + 1))) * Nat.card (K ≃+* K) := by rw [hc]
    _ ≤ (2 * Nat.card (elementaryProjective K (r + 1))) * Nat.card (K ≃+* K) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (center_card_le_two K r))
    _ = Nat.card (elementaryProjective K (r + 1)) * (2 * Nat.card (K ≃+* K)) := by ring

end SymmetricSubgroupAsymptotics.CFSGSymplecticPointRootLabels
