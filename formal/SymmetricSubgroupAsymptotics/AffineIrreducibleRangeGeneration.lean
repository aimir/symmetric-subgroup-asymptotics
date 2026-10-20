import SymmetricSubgroupAsymptotics.TernaryFourScalarAugmentation

/-! A subgroup of an irreducible affine group that projects onto its
actual complement and contains a nonzero translation is the whole group.
The elements lifting the complement may have arbitrary translation parts. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.AffineIrreducibleRangeGeneration

open SemidirectProduct TernaryFourAugmentationRepresentation

variable {R : Type} [Group R]
variable (b : R →* Equiv.Perm (Fin 4)) (s : R →* (ZMod 3)ˣ)

theorem eq_top_of_right_surjective
    (hirr : AffineModel.Irreducible (TernaryFourScalarAugmentation.linearGroup b s))
    (K : Subgroup (TernaryFourScalarAugmentation.Model b s))
    (hproj : ∀ r : R, ∃ g ∈ K, g.right = r)
    (v₀ : Vector) (hv₀ : v₀ ≠ 0) (hseed : inl (Multiplicative.ofAdd v₀) ∈ K) :
    K = ⊤ := by
  let S : AddSubgroup Vector := {
    carrier := {v | inl (Multiplicative.ofAdd v) ∈ K}
    zero_mem' := by simpa only [ofAdd_zero,map_one] using K.one_mem
    add_mem' := by
      intro x y hx hy
      change inl (Multiplicative.ofAdd (x+y)) ∈ K
      rw [ofAdd_add,map_mul]
      exact K.mul_mem hx hy
    neg_mem' := by
      intro x hx
      change inl (Multiplicative.ofAdd (-x)) ∈ K
      rw [ofAdd_neg,map_inv]
      exact K.inv_mem hx }
  have hstable : ∀ r ∈ TernaryFourScalarAugmentation.linearGroup b s,
      ∀ v ∈ S, r v ∈ S := by
    rintro r ⟨g,rfl⟩ v hv
    obtain ⟨h,hh,hr⟩ := hproj g
    have hc := K.mul_mem (K.mul_mem hh hv) (K.inv_mem hh)
    rw [LinearSemidirectCoprimeSocleBounds.conjugate_translation,hr] at hc
    exact hc
  have htop : S = ⊤ := by
    rcases hirr S hstable with hb | ht
    · have hv : v₀ ∈ S := hseed
      rw [hb] at hv
      exact (hv₀ (AddSubgroup.mem_bot.mp hv)).elim
    · exact ht
  have hleft (v : Multiplicative Vector) : inl v ∈ K := by
    have hv : v.toAdd ∈ S := by rw [htop]; exact AddSubgroup.mem_top _
    exact hv
  apply top_unique
  intro g _
  obtain ⟨h,hh,hr⟩ := hproj g.right
  have hinr : inr g.right ∈ K := by
    have hc := K.mul_mem (K.inv_mem (hleft h.left)) hh
    have he : (inl h.left)⁻¹ * h = inr g.right := by
      calc
        (inl h.left)⁻¹ * h = (inl h.left)⁻¹ * (inl h.left * inr h.right) :=
          congrArg (fun z => (inl h.left)⁻¹ * z) (inl_left_mul_inr_right h).symm
        _ = inr h.right := inv_mul_cancel_left _ _
        _ = inr g.right := congrArg inr hr
    rwa [he] at hc
  rw [← inl_left_mul_inr_right g]
  exact K.mul_mem (hleft g.left) hinr

theorem range_eq_closure_of_lifts
    (hirr : AffineModel.Irreducible (TernaryFourScalarAugmentation.linearGroup b s))
    {G : Type} [Group G] (f : TernaryFourScalarAugmentation.Model b s →* G)
    {ι : Type} (generators : ι → G)
    (lifts : ι → TernaryFourScalarAugmentation.Model b s)
    (hbind : ∀ i, f (lifts i) = generators i)
    (hgen : Subgroup.closure (Set.range (fun i => (lifts i).right)) = ⊤)
    (v₀ : Vector) (hv₀ : v₀ ≠ 0)
    (hseed : f (inl (Multiplicative.ofAdd v₀)) ∈ Subgroup.closure (Set.range generators)) :
    f.range = Subgroup.closure (Set.range generators) := by
  let T := Subgroup.closure (Set.range generators)
  let K := T.comap f
  have hl (i : ι) : lifts i ∈ K := by
    change f (lifts i) ∈ T
    rw [hbind]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  have hp : (⊤ : Subgroup R) ≤ K.map rightHom := by
    rw [← hgen]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨lifts i,hl i,rfl⟩
  have hK : K = ⊤ := eq_top_of_right_surjective b s hirr K
    (fun r => hp (Subgroup.mem_top r)) v₀ hv₀ hseed
  apply le_antisymm
  · rintro _ ⟨g,rfl⟩
    have hg : g ∈ K := by rw [hK]; exact Subgroup.mem_top _
    exact hg
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨lifts i,hbind i⟩

end SymmetricSubgroupAsymptotics.AffineIrreducibleRangeGeneration

end
