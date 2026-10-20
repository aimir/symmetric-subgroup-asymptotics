import Mathlib.GroupTheory.Abelianization.Defs

/-! Actual lift powers determine the exponent of the full original
abelianization. The kernel and the lift tuple remain in the same group;
no complement, splitting, or elementary-abelianization premise is used. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- If the kernel has exponent p, the original top images generate, and
the actual pth powers of those lifts lie in G', then the full
abelianization has exponent p. Finiteness and primality are unnecessary. -/
theorem abelianization_pow_eq_one_of_actual_lift_carries
    {G Q J : Type*} [Group G] [Group Q]
    (p : ℕ) (f : G →* Q) (u : J → G)
    (hgen : Subgroup.closure (Set.range fun j => f (u j)) = ⊤)
    (hker : ∀ k : f.ker, (k : G) ^ p = 1)
    (hlift : ∀ j, u j ^ p ∈ commutator G) :
    ∀ a : Abelianization G, a ^ p = 1 := by
  let b : G →* Abelianization G := (powMonoidHom p).comp Abelianization.of
  let P := b.ker
  have hKP : f.ker ≤ P := by
    intro k hk
    change (Abelianization.of k) ^ p = 1
    rw [← map_pow, hker ⟨k, hk⟩, map_one]
  have huP (j : J) : u j ∈ P := by
    change (Abelianization.of (u j)) ^ p = 1
    rw [← map_pow]
    apply MonoidHom.mem_ker.mp
    rw [Abelianization.ker_of]
    exact hlift j
  have hmap : P.map f = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply (Subgroup.closure_le (P.map f)).mpr
    rintro _ ⟨j, rfl⟩
    exact ⟨u j, huP j, rfl⟩
  have hP : P = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨a, ha, hag⟩ := (show f g ∈ P.map f by rw [hmap]; trivial)
    have hd : a⁻¹ * g ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hag, inv_mul_cancel]
    simpa only [mul_inv_cancel_left] using P.mul_mem ha (hKP hd)
  intro a
  refine QuotientGroup.induction_on a ?_
  intro g
  have hg : g ∈ P := by rw [hP]; trivial
  exact hg

end SymmetricSubgroupAsymptotics
