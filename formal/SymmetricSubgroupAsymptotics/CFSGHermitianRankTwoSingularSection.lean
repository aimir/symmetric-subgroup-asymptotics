import SymmetricSubgroupAsymptotics.CFSGHermitianThreeRayPencilFixation
import SymmetricSubgroupAsymptotics.CFSGHermitianPlaneMixedTest
import SymmetricSubgroupAsymptotics.CFSGHermitianMaximalGallery

/-! Generic singular-section determination from an actual signed trace
pencil. The finite-field caller proves that pencil condition; no point
map, source group, or geometric connectedness is supplied by a callback. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]

private theorem disjoint_components {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (P Z : Submodule K V) (hdis : Disjoint P Z) (x u y z : V)
    (hx : x ∈ P) (hu : u ∈ P) (hy : y ∈ Z) (hz : z ∈ Z) (he : x + y = u + z) :
    x = u ∧ y = z := by
  have hvec : x - u = z - y := by
    calc
      _ = (x + y) - (u + y) := by abel
      _ = (u + z) - (u + y) := by rw [he]
      _ = z - y := by abel
  have hzero : x - u = 0 := (Submodule.disjoint_def.mp hdis) _ (P.sub_mem hx hu)
    (by rw [hvec]; exact Z.sub_mem hz hy)
  have hxu := sub_eq_zero.mp hzero
  exact ⟨hxu, add_left_cancel (by simpa only [hxu] using he)⟩

theorem hermitian_rankTwo_fixes_singular_section (sig : K ≃+* K) (H : Matrix I I K)
    (P Z : Submodule K (I → K)) (hP : Orthogonal sig H P P) (hZ : Orthogonal sig H Z Z)
    (hdP : Module.finrank K P = 2) (hdZ : Module.finrank K Z = 2) (hdis : Disjoint P Z)
    (hNDz : ∀ z ∈ Z, (∀ x ∈ P, hermitianPair sig H z x = 0) → z = 0)
    (hswap : ∀ x y, hermitianPair sig H x y = 0 ↔ hermitianPair sig H y x = 0)
    (f : Equiv.Perm (SingularPoint sig H))
    (hlinear : ∀ M : MaximalSpace sig H,
      Nonempty (SemilinearPiece sig H f ⟨M.val, M.property.1⟩ (RingEquiv.refl K)))
    (hfixP : ∀ R : SingularPoint sig H, R.val ≤ P → f R = R)
    (hfixZ : ∀ R : SingularPoint sig H, R.val ≤ Z → f R = R)
    (hfixMixed : ∀ (x y : I → K), x ∈ P → x ≠ 0 → y ∈ Z → y ≠ 0 →
      hermitianPair sig H y x = 0 → ∀ R : SingularPoint sig H,
      R.val = K ∙ (x + y) → f R = R)
    (htrace : ∀ (x y u z : I → K), x ∈ P → u ∈ P → y ∈ Z → z ∈ Z →
      hermitianPair sig H (x + y) (x + y) = 0 → hermitianPair sig H z u = 0 →
      hermitianPair sig H x z = -hermitianPair sig H y u → hermitianPair sig H y u ≠ 0 →
      ∃ t t' : K, t ≠ t' ∧ hermitianPair sig H (y + t • z) (x + t • u) = 0 ∧
        hermitianPair sig H (y + t' • z) (x + t' • u) = 0) :
    ∀ R : SingularPoint sig H, R.val ≤ P ⊔ Z → f R = R := by
  classical
  intro R hRW
  obtain ⟨v, hvR, hv0⟩ := singularPoint_nonzero sig H R
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp (hRW hvR)
  have hRmem : x + y ∈ R.val := hxy.symm ▸ hvR
  have hsum0 : x + y ≠ 0 := hxy.symm ▸ hv0
  have hRspan := singularPoint_span sig H R (x + y) hRmem hsum0
  by_cases hx0 : x = 0
  · apply hfixZ R
    rw [hRspan]
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    simpa only [hx0, zero_add] using hy
  by_cases hy0 : y = 0
  · apply hfixP R
    rw [hRspan]
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    simpa only [hy0, add_zero] using hx
  by_cases hyx : hermitianPair sig H y x = 0
  · exact hfixMixed x y hx hx0 hy hy0 hyx R hRspan
  obtain ⟨u, hu, z, hz, hu0, hz0, hzu, hyu, hxz⟩ := exists_hermitian_plane_mixed_test sig H
    hswap P Z hdP hdZ
    hNDz x y hx hx0 hyx
  have hq0 : u + z ≠ 0 := by
    intro he
    have huZ : u ∈ Z := by rw [add_eq_zero_iff_eq_neg.mp he]; exact Z.neg_mem hz
    exact hu0 ((Submodule.disjoint_def.mp hdis) u hu huZ)
  have hli : LinearIndependent K ![x + y,u + z] := by
    apply (LinearIndependent.pair_iff' hsum0).mpr
    intro a he
    have hc := disjoint_components P Z hdis (a • x) u (a • y) z
      (P.smul_mem a hx) hu (Z.smul_mem a hy) hz (by simpa only [smul_add] using he)
    have ha : a ≠ 0 := by
      intro ha0
      rw [ha0, zero_smul] at he
      exact hq0 he.symm
    have hzero := hzu
    rw [← hc.1, ← hc.2, hermitianPair_smul] at hzero
    have hsig : sig a ≠ 0 := fun h => ha (sig.injective (h.trans (map_zero sig).symm))
    exact (mul_ne_zero (mul_ne_zero hsig ha) hyx) hzero
  have hqnorm : hermitianPair sig H (u + z) (u + z) = 0 := by
    rw [hermitianPair_add_left, hermitianPair_add_right, hermitianPair_add_right,
      hP u hu u hu,
      hZ z hz z hz,
      hzu, (hswap z u).mp hzu]
    simp only [zero_add]
  have hvnorm : hermitianPair sig H (x + y) (x + y) = 0 := R.property.2 _ hRmem
  have hvq : hermitianPair sig H (x + y) (u + z) = 0 := by
    rw [hermitianPair_add_left, hermitianPair_add_right, hermitianPair_add_right,
      hP x hx u hu,
      hZ y hy z hz, hxz]
    simp only [zero_add, add_zero, neg_add_cancel]
  let C := (K ∙ (x + y)) ⊔ K ∙ (u + z)
  have hC : Orthogonal sig H C C := by
    have hcross : Orthogonal sig H (K ∙ (x + y)) (K ∙ (u + z)) := by
      apply (orthogonal_span_left_iff sig H _ _).mpr
      intro w hw
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
      have hh := hermitianPair_smul sig H 1 a (x + y) (u + z)
      simpa only [one_smul, map_one, one_mul, hvq, mul_zero] using hh
    have hreverse : Orthogonal sig H (K ∙ (u + z)) (K ∙ (x + y)) :=
      fun a ha b hb => (hswap b a).mp (hcross b hb a ha)
    rw [orthogonal_sup_left_iff, orthogonal_sup_right_iff, orthogonal_sup_right_iff]
    exact ⟨⟨span_orthogonal_self sig H _ hvnorm, hcross⟩, hreverse, span_orthogonal_self sig H _ hqnorm⟩
  obtain ⟨M, hCM, hM⟩ := exists_maximalIsotropic_ge sig H C hC
  have hvm : x + y ∈ M := hCM ((show K ∙ (x + y) ≤ C from le_sup_left)
    (Submodule.mem_span_singleton_self _))
  have hqm : u + z ∈ M := hCM ((show K ∙ (u + z) ≤ C from le_sup_right)
    (Submodule.mem_span_singleton_self _))
  obtain ⟨F⟩ := hlinear ⟨M, hM⟩
  obtain ⟨t, t', htt, ht, ht'⟩ := htrace x y u z
    hx hu hy hz hvnorm hzu hxz hyu
  have hpencil (a : K) (ha : hermitianPair sig H (y + a • z) (x + a • u) = 0)
      (T : SingularPoint sig H) (hT : T.val = K ∙ ((x + y) + a • (u + z))) :
      f T = T := by
    have he : (x + y) + a • (u + z) = (x + a • u) + (y + a • z) := by module
    rw [he] at hT
    have hxP := P.add_mem hx (P.smul_mem a hu)
    have hyZ := Z.add_mem hy (Z.smul_mem a hz)
    by_cases hxa : x + a • u = 0
    · apply hfixZ T
      rw [hT, hxa, zero_add]
      exact (Submodule.span_singleton_le_iff_mem _ _).mpr hyZ
    by_cases hya : y + a • z = 0
    · apply hfixP T
      rw [hT, hya, add_zero]
      exact (Submodule.span_singleton_le_iff_mem _ _).mpr hxP
    exact hfixMixed _ _ hxP hxa hyZ hya ha T hT
  exact hermitian_three_pencil_rays_fix_base sig H f
    ⟨M, hM.1⟩ F (x + y) (u + z) hvm hqm hli t t' htt
    (fun T hT => hfixMixed u z hu hu0 hz hz0 hzu T hT)
    (hpencil t ht) (hpencil t' ht') R hRspan

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
