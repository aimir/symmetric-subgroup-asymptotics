import SymmetricSubgroupAsymptotics.CFSGPSLTwoBorelTwoOrbits
import SymmetricSubgroupAsymptotics.PointwiseProductOrbitEquiv
import SymmetricSubgroupAsymptotics.TwoOrbitProductSubsetLabels
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! ALL base orbits of the actual Borel product are labelled by subsets.
The correlated index-three cover is handled separately. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoProductBorelOrbitLabels
open CFSGPSLTwoGeometry CFSGPSLTwoBorelTwoOrbits
variable {F J : Type*} [Field F]

theorem transport_nonbase (x y : Points (F:=F)) (hx : x ≠ base) (hy : y ≠ base) :
    ∃ b : projectiveBorel (F:=F), b • y = x := by
  obtain ⟨a,ha⟩ := MulAction.mem_orbit_iff.mp ((base_or_opposite_orbit x).resolve_left hx)
  obtain ⟨b,hb⟩ := MulAction.mem_orbit_iff.mp ((base_or_opposite_orbit y).resolve_left hy)
  refine ⟨a*b⁻¹,?_⟩
  rw [mul_smul,←hb,inv_smul_smul,ha]

def labels : MulAction.orbitRel.Quotient
    (J → projectiveBorel (F:=F)) (J → Points (F:=F)) ≃ Set J :=
  TwoOrbitProductSubsetLabels.orbitLabels base opposite opposite_ne_base
    borel_fixes_base transport_nonbase

theorem labels_mk (x : J → Points (F:=F)) :
    labels (Quotient.mk _ x) = {i : J | x i ≠ base} := rfl

theorem base_orbit_card :
    Nat.card (MulAction.orbit (projectiveBorel (F:=F)) (base (F:=F))) = 1 := by
  let e : MulAction.orbit (projectiveBorel (F:=F)) (base (F:=F)) ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨base, MulAction.mem_orbit_iff.mpr ⟨1,one_smul _ _⟩⟩
      left_inv := by
        intro y
        apply Subtype.ext
        obtain ⟨b,hb⟩ := MulAction.mem_orbit_iff.mp y.property
        exact (borel_fixes_base b).symm.trans hb
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (by simp)

def maskPoint (s : Finset J) [DecidableEq J] : J → Points (F:=F) :=
  fun i => if i ∈ s then opposite else base

theorem maskPoint_orbit_card [Finite F] [Fintype J] [DecidableEq J] (s : Finset J) :
    Nat.card (MulAction.orbit (J → projectiveBorel (F:=F)) (maskPoint (F:=F) s)) =
      (Nat.card F)^s.card := by
  rw [PointwiseProductOrbitEquiv.card_orbit]
  have he (i : J) :
      Nat.card (MulAction.orbit (projectiveBorel (F:=F)) (maskPoint (F:=F) s i)) =
        if i ∈ s then Nat.card F else 1 := by
    by_cases hi : i ∈ s
    · simpa only [maskPoint,if_pos hi] using opposite_orbit_card (F:=F)
    · simpa only [maskPoint,if_neg hi] using base_orbit_card (F:=F)
  simp only [he]
  rw [Finset.prod_ite_mem_eq,Finset.prod_const]

end SymmetricSubgroupAsymptotics.CFSGPSLTwoProductBorelOrbitLabels
