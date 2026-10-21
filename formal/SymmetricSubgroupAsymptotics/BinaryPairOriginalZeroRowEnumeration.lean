import SymmetricSubgroupAsymptotics.BinaryPairSplitAffineRows
import SymmetricSubgroupAsymptotics.BinaryPairOriginalCoordinateRepresentation

/-! Exact row completeness in a literal original zero frame follows from
coordinate injectivity and the full semidirect-product cardinality. No
action table or normal-subgroup enumeration is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} {w r : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

theorem card_of_original_zero_frame (hzero : U = F.splitAffineAction) :
    Nat.card U = Nat.card F.kernelSpace * Nat.card F.top.range := by
  calc
    Nat.card U = Nat.card F.splitAffineAction :=
      Nat.card_congr (MulEquiv.subgroupCongr hzero).toEquiv
    _ = Nat.card F.SplitAffineModel :=
      (Nat.card_congr F.splitAffineModelEquiv.toEquiv).symm
    _ = Nat.card (Multiplicative F.kernelSpace) * Nat.card F.top.range := SemidirectProduct.card
    _ = Nat.card F.kernelSpace * Nat.card F.top.range := by
      rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative F.kernelSpace ≃ F.kernelSpace)]

def originalAffineRows (hzero : U = F.splitAffineAction)
    (topRow : Fin r → Equiv.Perm (Fin w)) (offsetRow : Fin r → Fin w → ZMod 2)
    (htop : ∀ i, topRow i ∈ F.top.range) (hoffset : ∀ i, offsetRow i ∈ F.kernelSpace) :
    Fin r → U := fun i => F.originalZeroRow hzero ⟨topRow i, htop i⟩ (offsetRow i) (hoffset i)

theorem originalAffineRows_injective (hzero : U = F.splitAffineAction)
    (topRow : Fin r → Equiv.Perm (Fin w)) (offsetRow : Fin r → Fin w → ZMod 2)
    (htop : ∀ i, topRow i ∈ F.top.range) (hoffset : ∀ i, offsetRow i ∈ F.kernelSpace)
    (hinj : ∀ i j, topRow i = topRow j → offsetRow i = offsetRow j → i = j) :
    Function.Injective (F.originalAffineRows hzero topRow offsetRow htop hoffset) := by
  intro i j he
  have hh := F.affinePermutation_coordinates_injective (congrArg Subtype.val he)
  exact hinj i j hh.1 hh.2

theorem originalAffineRows_bijective [Finite X] (hzero : U = F.splitAffineAction)
    (topRow : Fin r → Equiv.Perm (Fin w)) (offsetRow : Fin r → Fin w → ZMod 2)
    (htop : ∀ i, topRow i ∈ F.top.range) (hoffset : ∀ i, offsetRow i ∈ F.kernelSpace)
    (hinj : ∀ i j, topRow i = topRow j → offsetRow i = offsetRow j → i = j)
    (hcard : Nat.card F.kernelSpace * Nat.card F.top.range = r) :
    Function.Bijective (F.originalAffineRows hzero topRow offsetRow htop hoffset) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨F.originalAffineRows_injective hzero topRow offsetRow htop hoffset hinj, ?_⟩
  rw [Nat.card_fin, F.card_of_original_zero_frame hzero, hcard]

theorem originalCoordinateRepresentation_affineRow (hzero : U = F.splitAffineAction)
    (topRow : Fin r → Equiv.Perm (Fin w)) (offsetRow : Fin r → Fin w → ZMod 2)
    (htop : ∀ i, topRow i ∈ F.top.range) (hoffset : ∀ i, offsetRow i ∈ F.kernelSpace)
    (i : Fin r) :
    F.originalCoordinateRepresentation (F.originalAffineRows hzero topRow offsetRow htop hoffset i) =
      pairLayerFlatten.toLinearMap.comp
        ((affinePairLayerMap (topRow i) (offsetRow i)).comp pairLayerFlatten.symm.toLinearMap) :=
  F.originalCoordinateRepresentation_zeroRow hzero ⟨topRow i, htop i⟩ (offsetRow i) (hoffset i)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
