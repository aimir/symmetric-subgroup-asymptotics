import SymmetricSubgroupAsymptotics.CFSGSymplecticOddOuterCardinality
import SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyActionFaithfulness

/-! A root-family-preserving subgroup of the actual projective
symplectic automorphism group is counted through PGSp and field maps.
Its actual index is charged before cancelling the inner group. -/
set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticPointRootLabels
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
open CFSGSymplecticCollineationSimilitudes PrimitiveSocleRawStructure
variable {K : Type} [Field K] [Finite K]

def familyOrthogonalHom (r : ℕ) (hr : 0 < r)
    (S : Subgroup (MulAut (elementaryProjective K (r + 1))))
    (hstable : ∀ f : S, ∀ x : Points (K := K) r,
      ∃ y, label r hr y = (label r hr x).map f.val.toMonoidHom) :
    S →* orthogonalGroup (K := K) (r + 1) := by
  let pi := CFSGSubgroupFamilyAction.permutationHom S.subtype (label r hr)
    (label_injective r hr) hstable
  have hlabel (f : S) (x : Points (K := K) r) :
      label r hr (pi f x) = (label r hr x).map f.val.toMonoidHom :=
    CFSGSubgroupFamilyAction.label_permutation S.subtype (label r hr) (label_injective r hr)
      hstable f x
  exact {
    toFun := fun f => ⟨⟨pi f, collineation_of_label_map r hr f.val _ (hlabel f)⟩,
      orthogonal_iff_of_label_map r hr f.val _ (hlabel f)⟩
    map_one' := Subtype.ext (Subtype.ext pi.map_one)
    map_mul' := fun f g => Subtype.ext (Subtype.ext (pi.map_mul f g)) }

theorem familyOrthogonalHom_injective (r : ℕ) (hr : 0 < r)
    [IsSimpleGroup (elementaryProjective K (r + 1))]
    (S : Subgroup (MulAut (elementaryProjective K (r + 1))))
    (hinner : ∀ g, MulAut.conj g ∈ S)
    (hstable : ∀ f : S, ∀ x : Points (K := K) r,
      ∃ y, label r hr y = (label r hr x).map f.val.toMonoidHom) :
    Function.Injective (familyOrthogonalHom r hr S hstable) := by
  let v : Index (r + 1) → K := Pi.single (Sum.inl 0) 1
  have hv : v ≠ 0 := by intro h; have hh := congrFun h (Sum.inl 0); simp [v] at hh
  let x := Projectivization.mk K v hv
  have hi := CFSGSubgroupFamilyActionFaithfulness.permutationHom_injective S hinner
    (label r hr) (label_injective r hr) hstable x (label_ne_bot r hr x) (label_ne_top r hr x)
  intro f g h
  apply hi
  exact congrArg (fun a : orthogonalGroup (K := K) (r + 1) => a.val.val) h

theorem family_subgroup_card_le (r : ℕ) (hr : 0 < r)
    [IsSimpleGroup (elementaryProjective K (r + 1))]
    (S : Subgroup (MulAut (elementaryProjective K (r + 1))))
    (hinner : ∀ g, MulAut.conj g ∈ S)
    (hstable : ∀ f : S, ∀ x : Points (K := K) r,
      ∃ y, label r hr y = (label r hr x).map f.val.toMonoidHom) :
    Nat.card S ≤ Nat.card (elementaryRootGroup K (r + 1)) * Nat.card (K ≃+* K) := by
  let b : Index (r + 1) := Sum.inl 0
  let i : Index (r + 1) := Sum.inl ⟨1, by omega⟩
  let j : Index (r + 1) := Sum.inr 0
  exact (Nat.card_le_card_of_injective _ (familyOrthogonalHom_injective r hr S hinner hstable)).trans
    (orthogonalGroup_card_le (r + 1) (by omega) b i j (by simp [b, i, Fin.ext_iff])
      (by simp [b, j]) (by simp [i, j]))

theorem family_outer_card_le (r : ℕ) (hr : 0 < r)
    [IsSimpleGroup (elementaryProjective K (r + 1))]
    (S : Subgroup (MulAut (elementaryProjective K (r + 1))))
    (hinner : ∀ g, MulAut.conj g ∈ S)
    (hstable : ∀ f : S, ∀ x : Points (K := K) r,
      ∃ y, label r hr y = (label r hr x).map f.val.toMonoidHom)
    (d : ℕ) (hindex : S.index ≤ d) :
    Nat.card (Outer (elementaryProjective K (r + 1))) ≤
      d * Nat.card (Subgroup.center (elementaryRootGroup K (r + 1))) * Nat.card (K ≃+* K) := by
  have hS := family_subgroup_card_le r hr S hinner hstable
  have hc := (Subgroup.center (elementaryRootGroup K (r + 1))).card_mul_index
  change Nat.card (Subgroup.center (elementaryRootGroup K (r + 1))) *
    Nat.card (elementaryProjective K (r + 1)) = Nat.card (elementaryRootGroup K (r + 1)) at hc
  apply CFSGOuterCardinalityCancellation.outer_card_le_of_automorphism_bound (projective_noncommutative r hr)
  calc
    Nat.card (MulAut (elementaryProjective K (r + 1))) = Nat.card S * S.index := S.card_mul_index.symm
    _ ≤ (Nat.card (elementaryRootGroup K (r + 1)) * Nat.card (K ≃+* K)) * d :=
      Nat.mul_le_mul hS hindex
    _ = Nat.card (elementaryProjective K (r + 1)) *
      (d * Nat.card (Subgroup.center (elementaryRootGroup K (r + 1))) * Nat.card (K ≃+* K)) := by
      rw [← hc]
      ring

end SymmetricSubgroupAsymptotics.CFSGSymplecticPointRootLabels
