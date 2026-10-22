import SymmetricSubgroupAsymptotics.CFSGOrthogonalBAdjacentRootProducts
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBRootProductIntersection

/-! Exact intrinsic adjacency: two distinct original B root subgroups
admit commuting nonidentity elements with long-root product if and only
if their SAME natural two-planes meet in a point and have singular sum.
This includes rank three and assumes no polar graph reconstruction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent
variable {K : Type} [Field K] [Finite K]

def PlaneAdjacent (s : ℕ) (P Q : Submodule K (Index (s + 3) → K)) : Prop :=
  P ≠ Q ∧ Module.finrank K (P ⊓ Q : Submodule K (Index (s + 3) → K)) = 1 ∧
    IsTotallySingular (K := K) s (P ⊔ Q)

def RootAdjacent (s : ℕ) (L M : Subgroup (elementaryRootGroup K (s + 3))) : Prop :=
  L ≠ M ∧ ∃ x ∈ L, x ≠ 1 ∧ ∃ y ∈ M, y ≠ 1 ∧ Commute x y ∧ IsLongRootElement s (x * y)

private theorem singular_sup_of_cross (s : ℕ) (P Q : Submodule K (Index (s + 3) → K))
    (hP : IsTotallySingular (K := K) s P) (hQ : IsTotallySingular (K := K) s Q)
    (hc : ∀ u ∈ P, ∀ v ∈ Q, (gram K (s + 3)).toBilin' u v = 0) :
    IsTotallySingular (K := K) s (P ⊔ Q) := by
  rintro u hu v hv
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hu
  obtain ⟨p', hp', q', hq', rfl⟩ := Submodule.mem_sup.mp hv
  have hrev : (gram K (s + 3)).toBilin' q p' = 0 :=
    (gram_pairing_symmetric (s + 3) q p').trans (hc p' hp' q hq)
  simp only [map_add, LinearMap.add_apply]
  rw [hP p hp p' hp', hc p hp q' hq', hrev, hQ q hq q' hq']
  simp

theorem rootAdjacent_iff_planeAdjacent (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g h : elementaryRootGroup K (s + 3)) :
    RootAdjacent s (conjugateRootLine h2 s g) (conjugateRootLine h2 s h) ↔
      PlaneAdjacent s (conjugateRootPlane (K := K) s g) (conjugateRootPlane (K := K) s h) := by
  constructor
  · rintro ⟨hne, x, hxL, hxn, y, hyL, hyn, hc, hp⟩
    have hplanes : conjugateRootPlane (K := K) s g ≠ conjugateRootPlane (K := K) s h :=
      fun he => hne ((conjugateRootLine_eq_iff_plane_eq h2 s g h).mpr he)
    obtain ⟨a, rfl⟩ := (mem_conjugateRootLine_iff_exists h2 s g x).mp hxL
    obtain ⟨b, rfl⟩ := (mem_conjugateRootLine_iff_exists h2 s h y).mp hyL
    have ha : a ≠ 0 := by
      intro he
      apply hxn
      rw [he, highestRoot_zero h2 s, mul_one, mul_inv_cancel]
    have hb : b ≠ 0 := by
      intro he
      apply hyn
      rw [he, highestRoot_zero h2 s, mul_one, mul_inv_cancel]
    refine ⟨hplanes, root_product_distinct_planes_intersect_in_point h2 s g h a b ha hb hc hp hplanes, ?_⟩
    exact singular_sup_of_cross s _ _ (conjugateRootPlane_totallySingular h2 s g)
      (conjugateRootPlane_totallySingular h2 s h)
      (root_product_planes_orthogonal h2 s g h a b ha hb hc hp)
  · rintro ⟨hne, hdim, hs⟩
    have hline : conjugateRootLine h2 s g ≠ conjugateRootLine h2 s h :=
      fun he => hne ((conjugateRootLine_eq_iff_plane_eq h2 s g h).mp he)
    have hmeet : conjugateRootPlane (K := K) s g ⊓ conjugateRootPlane (K := K) s h ≠ ⊥ := by
      intro he
      have hd := congrArg (fun P : Submodule K (Index (s + 3) → K) => Module.finrank K P) he
      have hz : Module.finrank K (conjugateRootPlane (K := K) s g ⊓
          conjugateRootPlane (K := K) s h : Submodule K (Index (s + 3) → K)) = 0 :=
        hd.trans (finrank_bot K (Index (s + 3) → K))
      omega
    exact ⟨hline, adjacent_planes_have_root_product h2 s g h hne hmeet hs⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
