import SymmetricSubgroupAsymptotics.CFSGSymplecticIntrinsicRootLines
import SymmetricSubgroupAsymptotics.CFSGSymplecticPolarity
import SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyAction

/-! Literal projective points label exactly the original natural-root
subgroups. The label is injective in every characteristic, and odd-field
projective automorphisms preserve this actual labelled family. -/
set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticPointRootLabels
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
variable {K : Type} [Field K]

abbrev Points (r : ℕ) := ℙ K (Index (r + 1) → K)

def label (r : ℕ) (hr : 0 < r) (p : Points (K := K) r) :
    Subgroup (elementaryProjective K (r + 1)) := projectiveNaturalRootLine r hr p.rep

theorem label_mk (r : ℕ) (hr : 0 < r) (v : Index (r + 1) → K) (hv : v ≠ 0) :
    label r hr (Projectivization.mk K v hv) = projectiveNaturalRootLine r hr v := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  change projectiveNaturalRootLine r hr (Projectivization.mk K v hv).rep = _
  rw [← ha]
  exact projectiveNaturalRootLine_smul r hr v a.val a.ne_zero

theorem label_injective (r : ℕ) (hr : 0 < r) :
    Function.Injective (label (K := K) r hr) := by
  intro p q he
  obtain ⟨c, hc, hv⟩ := (projectiveNaturalRootLine_eq_iff r hr p.rep q.rep
    p.rep_nonzero).mp he
  rw [← Projectivization.mk_rep p, ← Projectivization.mk_rep q]
  exact (Projectivization.mk_eq_mk_iff K _ _ _ _).mpr ⟨Units.mk0 c hc, hv.symm⟩

theorem label_card [Finite K] (r : ℕ) (hr : 0 < r) (p : Points (K := K) r) :
    Nat.card (label r hr p) = Nat.card K :=
  projectiveNaturalRootLine_card r hr p.rep p.rep_nonzero

theorem odd_stable [Finite K] (p r : ℕ) [Fact p.Prime] [CharP K p]
    (hr : 0 < r) (htwo : (2 : K) ≠ 0)
    (f : MulAut (elementaryProjective K (r + 1))) (x : Points (K := K) r) :
    ∃ y, label r hr y = (label r hr x).map f.toMonoidHom := by
  obtain ⟨w, hw, he⟩ :=
    CFSGSymplecticProjectiveOddRootRecognition.automorphism_maps_projectiveNaturalRootLine
      p r hr htwo f x.rep x.rep_nonzero
  exact ⟨Projectivization.mk K w hw, (label_mk r hr w hw).trans he.symm⟩

end SymmetricSubgroupAsymptotics.CFSGSymplecticPointRootLabels
