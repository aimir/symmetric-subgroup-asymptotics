import SymmetricSubgroupAsymptotics.BinaryPairFullKernelGenerators

/-! Even pair flips suffice for kernel sharing when one original element
has odd total offset. Nonconstant pair-sum vectors give an individual
pair constant. Constant nonzero pair-sum vectors give the even kernel,
and the odd-offset displacement supplies its remaining direction.
Every group element and every module is attached to the original frame. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} [Fintype I] [DecidableEq I]
  {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)

private theorem binary_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Transitivity spreads one individual pair constant to the full kernel. -/
theorem pairSum_kernel_le_of_single_mem
    (htrans : ∀ i j : I, ∃ u : U, F.top u i = j)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (i : I) (hi : F.pairConstant (Pi.single i (1 : ZMod 2)) ∈ W.toSubmodule) :
    F.pairSum.ker ≤ W.toSubmodule := by
  have hall (j : I) : F.pairConstant (Pi.single j (1 : ZMod 2)) ∈ W.toSubmodule := by
    obtain ⟨u, hu⟩ := htrans i j
    have h := W.apply_mem_toSubmodule u hi
    rw [F.pairConstant_action] at h
    have he : (fun t ↦ (Pi.single i 1 : I → ZMod 2) ((F.top u)⁻¹ t)) =
        (Pi.single j 1 : I → ZMod 2) := by
      funext t
      have ht : (F.top u)⁻¹ t = i ↔ t = j := by
        constructor
        · intro hit
          calc
            t = F.top u ((F.top u)⁻¹ t) := ((F.top u).apply_symm_apply t).symm
            _ = F.top u i := congrArg (F.top u) hit
            _ = j := hu
        · intro htj
          rw [htj, ← hu]
          exact (F.top u).symm_apply_apply i
      simp only [Pi.single_apply, ht]
    rwa [he] at h
  have hconstant (a : I → ZMod 2) : F.pairConstant a ∈ W.toSubmodule := by
    have hdecomp : (∑ j, a j • Pi.single j (1 : ZMod 2)) = a := by
      calc
        _ = ∑ j, Pi.single j (a j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [← Pi.single_smul]
          simp
        _ = a := LinearMap.sum_single_apply (fun _ : I ↦ ZMod 2) a
    rw [← hdecomp, map_sum]
    exact W.toSubmodule.sum_mem fun j _ ↦ by
      rw [map_smul]
      exact W.toSubmodule.smul_mem _ (hall j)
  intro f hf
  have hf' : f ∈ LinearMap.range F.pairConstantIntertwiner.toLinearMap := by
    rw [F.pairConstant_pairSum_exact_linear]
    exact hf
  obtain ⟨a, rfl⟩ := hf'
  exact hconstant a

/-- Odd total offset makes the pair-sum kernel comparable with every
invariant subspace, provided all even pair flips are actually present. -/
theorem pairSum_kernel_comparable_of_even_and_odd
    (hflip : ∀ i j : I, ∃ k : F.top.ker,
      F.bits k = Pi.single i (1 : ZMod 2) + Pi.single j (1 : ZMod 2))
    (htrans : ∀ i j : I, ∃ u : U, F.top u i = j)
    (hodd : ∃ u : U, ∑ i, F.offset u i = 1)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hW : ¬ W.toSubmodule ≤ F.pairSum.ker) :
    F.pairSum.ker ≤ W.toSubmodule := by
  have hv : ∃ v ∈ W.toSubmodule, F.pairSum v ≠ 0 := by
    by_contra hn
    apply hW
    intro v hv
    change F.pairSum v = 0
    by_contra hz
    exact hn ⟨v, hv, hz⟩
  obtain ⟨v, hv, hsum⟩ := hv
  have hi : ∃ i, F.pairSum v i ≠ 0 := by
    by_contra hn
    apply hsum
    funext i
    by_contra hz
    exact hn ⟨i, hz⟩
  obtain ⟨i, hi⟩ := hi
  have hi1 : F.pairSum v i = 1 := (binary_cases _).resolve_left hi
  apply F.pairSum_kernel_le_of_single_mem htrans W i
  by_cases hz : ∃ j, F.pairSum v j = 0
  · obtain ⟨j, hj⟩ := hz
    obtain ⟨k, hk⟩ := hflip i j
    have h := W.toSubmodule.sub_mem (W.apply_mem_toSubmodule (k : U) hv) hv
    rw [F.kernel_displacement_eq_pairConstant_product, hk] at h
    have he : (fun x ↦ ((Pi.single i 1 : I → ZMod 2) x +
        (Pi.single j 1 : I → ZMod 2) x) * F.pairSum v x) =
          (Pi.single i 1 : I → ZMod 2) := by
      funext x
      rw [add_mul]
      have hfirst : (Pi.single i 1 : I → ZMod 2) x * F.pairSum v x =
          (Pi.single i 1 : I → ZMod 2) x := by
        by_cases hx : x = i
        · subst x; simp [hi1]
        · simp [hx]
      have hsecond : (Pi.single j 1 : I → ZMod 2) x * F.pairSum v x = 0 := by
        by_cases hx : x = j
        · subst x; simp [hj]
        · simp [hx]
      rw [hfirst, hsecond, add_zero]
    change F.pairConstant (fun x ↦ ((Pi.single i 1 : I → ZMod 2) x +
      (Pi.single j 1 : I → ZMod 2) x) * F.pairSum v x) ∈ W.toSubmodule at h
    rwa [he] at h
  · have hone (j : I) : F.pairSum v j = 1 :=
      (binary_cases _).resolve_left (fun hj ↦ hz ⟨j, hj⟩)
    have hdouble (j : I) :
        F.pairConstant (Pi.single j (1 : ZMod 2) + Pi.single i (1 : ZMod 2)) ∈
          W.toSubmodule := by
      obtain ⟨k, hk⟩ := hflip j i
      have h := W.toSubmodule.sub_mem (W.apply_mem_toSubmodule (k : U) hv) hv
      rw [F.kernel_displacement_eq_pairConstant_product, hk] at h
      simpa only [hone, mul_one] using h
    have hvalue (j : I) (b : ZMod 2) :
        v (F.frame (j, b)) = v (F.frame (j, 0)) + b := by
      rcases binary_cases b with rfl | rfl
      · exact (add_zero _).symm
      · have hj : v (F.frame (j, 0)) + v (F.frame (j, 1)) = 1 := hone j
        have he := congrArg (fun z : ZMod 2 ↦ v (F.frame (j, 0)) + z) hj
        simpa only [← add_assoc, CharTwo.add_self_eq_zero, zero_add] using he
    obtain ⟨u, hu⟩ := hodd
    let a : I → ZMod 2 := fun j ↦
      v (F.frame (F.top u j, 0)) + F.offset u j - v (F.frame (j, 0))
    have ha : F.pairConstant a ∈ W.toSubmodule := by
      have h := W.toSubmodule.sub_mem (W.apply_mem_toSubmodule u⁻¹ hv) hv
      have he : permutationFunctionRepresentation (ZMod 2) U X u⁻¹ v - v =
          F.pairConstant a := by
        funext x
        obtain ⟨⟨j, b⟩, rfl⟩ := F.frame.surjective x
        change v ((((u⁻¹)⁻¹ : U) : Equiv.Perm X) (F.frame (j, b))) -
          v (F.frame (j, b)) = F.pairConstant a (F.frame (j, b))
        rw [inv_inv, F.action_frame, F.pairConstant_frame,
          hvalue (F.top u j) (b + F.offset u j), hvalue j b]
        dsimp [a]
        ring
      rwa [he] at h
    have hsum_a : ∑ j, a j = 1 := by
      dsimp [a]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Equiv.sum_comp (F.top u) (fun j ↦ v (F.frame (j, 0))), hu]
      ring
    have hdecomp :
        (∑ j, a j • (Pi.single j (1 : ZMod 2) + Pi.single i (1 : ZMod 2))) =
          a + Pi.single i (1 : ZMod 2) := by
      simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hsum_a, one_smul]
      congr 1
      calc
        _ = ∑ j, Pi.single j (a j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [← Pi.single_smul]
          simp
        _ = a := LinearMap.sum_single_apply (fun _ : I ↦ ZMod 2) a
    have hb : F.pairConstant (a + Pi.single i (1 : ZMod 2)) ∈ W.toSubmodule := by
      rw [← hdecomp, map_sum]
      exact W.toSubmodule.sum_mem fun j _ ↦ by
        rw [map_smul]
        exact W.toSubmodule.smul_mem _ (hdouble j)
    have h := W.toSubmodule.add_mem ha hb
    rw [map_add, ← add_assoc] at h
    have hzero : F.pairConstant a + F.pairConstant a = 0 := by
      funext x
      exact CharTwo.add_self_eq_zero (F.pairConstant a x)
    rwa [hzero, zero_add] at h

/-- The pair module's uniform budget is shared by the full point module
under the weaker even-flip and odd-offset hypotheses. -/
theorem uniform_of_even_pair_kernel_and_odd_offset
    (hflip : ∀ i j : I, ∃ k : F.top.ker,
      F.bits k = Pi.single i (1 : ZMod 2) + Pi.single j (1 : ZMod 2))
    (htrans : ∀ i j : I, ∃ u : U, F.top u i = j)
    (hodd : ∃ u : U, ∑ i, F.offset u i = 1)
    (n : ℕ)
    (hpair : UniformSubrepresentationGeneratorBound F.pulledBackCoordinateTopAction n) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) n := by
  let rho := permutationFunctionRepresentation (ZMod 2) U X
  let sigma := F.pulledBackCoordinateTopAction
  let i : sigma.asModule →ₗ[(ZMod 2)[U]] rho.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule sigma rho
      F.pairConstantIntertwiner
  let q : rho.asModule →ₗ[(ZMod 2)[U]] sigma.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule rho sigma
      F.pairSumIntertwiner
  apply (uniformSubrepresentationGeneratorBound_iff_submodule rho n).mpr
  have hp := (uniformSubrepresentationGeneratorBound_iff_submodule sigma n).mp hpair
  apply ModuleGeneratedBy.uniform_of_comparable_exact i q
    F.pairConstantIntertwiner_injective F.pairConstant_pairSum_exact n hp hp
  intro S hS
  let W : Subrepresentation rho := Subrepresentation.ofSubmodule' S
  have hW : ¬ W.toSubmodule ≤ F.pairSum.ker := by
    intro h
    apply hS
    intro x hx
    exact h hx
  exact F.pairSum_kernel_comparable_of_even_and_odd hflip htrans hodd W hW

/-- Intrinsic range form for a literal pair-top certificate. -/
theorem uniform_of_even_pair_kernel_and_odd_offset_coordinateTop
    (hflip : ∀ i j : I, ∃ k : F.top.ker,
      F.bits k = Pi.single i (1 : ZMod 2) + Pi.single j (1 : ZMod 2))
    (htrans : ∀ i j : I, ∃ u : U, F.top u i = j)
    (hodd : ∃ u : U, ∑ i, F.offset u i = 1)
    (n : ℕ)
    (hpair : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range I) n) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) n :=
  F.uniform_of_even_pair_kernel_and_odd_offset hflip htrans hodd n
    (UniformSubrepresentationGeneratorBound.comp_of_surjective
      (permutationFunctionRepresentation (ZMod 2) F.top.range I)
      F.top.rangeRestrict F.top.rangeRestrict_surjective hpair)

end SymmetricSubgroupAsymptotics.BinaryPairFrame

end
