import SymmetricSubgroupAsymptotics.CFSGSymplecticPointRootLabels

/-! Every actual automorphism preserving the labelled natural-root
family induces an orthogonality-preserving permutation of original
projective points, hence an actual projective collineation. -/
set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticPointRootLabels
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
variable {K : Type} [Field K]

private theorem mapped_root_parameter (r : ℕ) (hr : 0 < r)
    (f : MulAut (elementaryProjective K (r + 1)))
    (e : Equiv.Perm (Points (K := K) r))
    (he : ∀ p, label r hr (e p) = (label r hr p).map f.toMonoidHom)
    (p : Points (K := K) r) :
    ∃ a : K, a ≠ 0 ∧
      projectiveNaturalRootHom r hr (e p).rep (Multiplicative.ofAdd a) =
        f (projectiveNaturalRootHom r hr p.rep (Multiplicative.ofAdd 1)) := by
  have hm : f (projectiveNaturalRootHom r hr p.rep (Multiplicative.ofAdd 1)) ∈
      (label r hr p).map f.toMonoidHom :=
    ⟨_, ⟨Multiplicative.ofAdd 1, rfl⟩, rfl⟩
  rw [← he p] at hm
  obtain ⟨a, ha⟩ := hm
  refine ⟨a.toAdd, ?_, ha⟩
  intro hz
  have ha0 : a = 1 := Multiplicative.toAdd.injective hz
  have hf : f (projectiveNaturalRootHom r hr p.rep (Multiplicative.ofAdd 1)) = 1 := by
    rw [← ha, ha0, map_one]
  have hsource := f.injective (hf.trans f.map_one.symm)
  have hparam := projectiveNaturalRootHom_injective r hr p.rep p.rep_nonzero
    (hsource.trans (projectiveNaturalRootHom r hr p.rep).map_one.symm)
  exact one_ne_zero (congrArg Multiplicative.toAdd hparam)

theorem orthogonal_iff_of_label_map (r : ℕ) (hr : 0 < r)
    (f : MulAut (elementaryProjective K (r + 1)))
    (e : Equiv.Perm (Points (K := K) r))
    (he : ∀ p, label r hr (e p) = (label r hr p).map f.toMonoidHom)
    (p q : Points (K := K) r) :
    CFSGSymplecticPolarity.Orthogonal K (r + 1) (e p) (e q) ↔
      CFSGSymplecticPolarity.Orthogonal K (r + 1) p q := by
  obtain ⟨a, ha, hpa⟩ := mapped_root_parameter r hr f e he p
  obtain ⟨b, hb, hqb⟩ := mapped_root_parameter r hr f e he q
  change pairing (r + 1) (e p).rep (e q).rep = 0 ↔ pairing (r + 1) p.rep q.rep = 0
  rw [← projectiveNaturalRootElement_commute_iff r hr _ _ a b ha hb,
    hpa, hqb, commute_map_iff f.injective,
    projectiveNaturalRootElement_commute_iff r hr _ _ (1 : K) 1 one_ne_zero one_ne_zero]

theorem collineation_of_label_map (r : ℕ) (hr : 0 < r)
    (f : MulAut (elementaryProjective K (r + 1)))
    (e : Equiv.Perm (Points (K := K) r))
    (he : ∀ p, label r hr (e p) = (label r hr p).map f.toMonoidHom) :
    e ∈ CFSGProjectiveFrameCoordinates.collineationGroup (F := K) (n := Index (r + 1)) :=
  CFSGSymplecticPolarity.orthogonal_permutation_mem_collineation K (r + 1) e
    (orthogonal_iff_of_label_map r hr f e he)

end SymmetricSubgroupAsymptotics.CFSGSymplecticPointRootLabels
