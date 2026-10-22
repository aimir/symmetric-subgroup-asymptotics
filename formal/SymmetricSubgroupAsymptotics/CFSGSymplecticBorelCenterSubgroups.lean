import SymmetricSubgroupAsymptotics.CFSGSymplecticCenterScalarTests
import SymmetricSubgroupAsymptotics.CFSGTwoWeightAdditiveSubgroups

/-! Every actual Borel-normalized subgroup of the actual
characteristic-two centre has only the four coordinate possibilities.
This is a theorem about its literal coordinate preimage, not a new
classification input or a replacement definition of the source group. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices
variable {K : Type} [Field K] [Finite K] [CharP K 2]

def centerToElementary (r : ℕ) (hr : 0 < r) :
    Multiplicative (K × K) →* elementaryRootGroup K (r + 1) :=
  (unipotent K (r + 1)).subtype.comp
    ((Subgroup.center (unipotent K (r + 1))).subtype.comp (centerParameterHom r hr))

def centerCoordinatePreimage (r : ℕ) (hr : 0 < r)
    (H : Subgroup (elementaryRootGroup K (r + 1))) : AddSubgroup (K × K) :=
  (H.comap (centerToElementary r hr)).toAddSubgroup'

theorem centerCoordinatePreimage_classification (r : ℕ) (hr : 0 < r)
    (H : Subgroup (elementaryRootGroup K (r + 1)))
    (hH : borel K (r + 1) ≤ Subgroup.normalizer (H : Set (elementaryRootGroup K (r + 1))))
    (u : Kˣ) (hu : (u : K) ≠ 1) :
    centerCoordinatePreimage r hr H = ⊥ ∨
      centerCoordinatePreimage r hr H = CFSGTwoWeightAdditiveSubgroups.leftAxis ∨
      centerCoordinatePreimage r hr H = CFSGTwoWeightAdditiveSubgroups.rightAxis ∨
      centerCoordinatePreimage r hr H = ⊤ := by
  apply CFSGTwoWeightAdditiveSubgroups.classification _ ?_ ?_ u hu
  · intro v x hx
    change (centerParameterElement r hr x.1 x.2).val ∈ H at hx
    obtain ⟨g, hg⟩ := exists_left_center_scalar r hr v
    have hh := (Subgroup.mem_normalizer_iff.mp (hH g.property)
      (centerParameterElement r hr x.1 x.2).val).mp hx
    change (centerParameterElement r hr ((v : K) * x.1) x.2).val ∈ H
    rw [← hg x.1 x.2]
    exact hh
  · intro v x hx
    change (centerParameterElement r hr x.1 x.2).val ∈ H at hx
    obtain ⟨g, hg⟩ := exists_right_center_scalar r hr v
    have hh := (Subgroup.mem_normalizer_iff.mp (hH g.property)
      (centerParameterElement r hr x.1 x.2).val).mp hx
    change (centerParameterElement r hr x.1 ((v : K) * x.2)).val ∈ H
    rw [← hg x.1 x.2]
    exact hh

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
