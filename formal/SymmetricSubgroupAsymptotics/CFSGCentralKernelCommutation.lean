import SymmetricSubgroupAsymptotics.CFSGCentralKernelPElements

/-! Projective commutation with a p-element lifts through a central
kernel when the homomorphism is injective on an actual Sylow subgroup.
Only the p-element and its conjugate are compared; no automorphism lift
or prime-to-centre cardinality premise is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCentralKernelCommutation
variable {G H : Type*} [Group G] [Group H] {p : ℕ} [Fact p.Prime]

theorem commute_of_map_commute (f : G →* H) (P : Sylow p G)
    (hP : Function.Injective (f.comp (P : Subgroup G).subtype))
    (hker : f.ker ≤ Subgroup.center G) (x y : G)
    (hx : ∃ k : ℕ, x ^ p ^ k = 1) (hxy : Commute (f x) (f y)) :
    Commute x y := by
  have hyx : ∃ k : ℕ, ((MulAut.conj y) x) ^ p ^ k = 1 := by
    obtain ⟨k,hk⟩ := hx
    refine ⟨k,?_⟩
    rw [← map_pow,hk,map_one]
  have he : f ((MulAut.conj y) x) = f x := by
    change f (y*x*y⁻¹) = f x
    calc
      _ = (f y*f x)*(f y)⁻¹ := by rw [map_mul,map_mul,map_inv]
      _ = (f x*f y)*(f y)⁻¹ := congrArg (fun z => z*(f y)⁻¹) hxy.eq.symm
      _ = f x := by group
  have hconj := CFSGCentralKernelPElements.eq_of_p_elements f P hP hker
    ((MulAut.conj y) x) x hyx hx he
  have hh := congrArg (fun z : G => z*y) hconj
  change (y*x*y⁻¹)*y = x*y at hh
  change x*y = y*x
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh.symm

theorem map_commute_iff (f : G →* H) (P : Sylow p G)
    (hP : Function.Injective (f.comp (P : Subgroup G).subtype))
    (hker : f.ker ≤ Subgroup.center G) (x y : G)
    (hx : ∃ k : ℕ, x ^ p ^ k = 1) : Commute (f x) (f y) ↔ Commute x y := by
  constructor
  · exact commute_of_map_commute f P hP hker x y hx
  · intro h
    change f x*f y = f y*f x
    rw [← map_mul,← map_mul,h.eq]

end SymmetricSubgroupAsymptotics.CFSGCentralKernelCommutation
