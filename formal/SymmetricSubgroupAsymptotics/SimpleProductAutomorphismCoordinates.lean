import SymmetricSubgroupAsymptotics.SemisimpleOuterFibre

/-! Literal coordinate routing of onto maps from a product of copies of
a finite nonabelian simple group. The source factors, rather than an
abstract product recognition, are retained. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.SimpleProductAutomorphismCoordinates

variable {I T : Type} [Fintype I] [Group T] [Finite T]
    [IsSimpleGroup T] (hT : IsCenterless T)

include hT in
/-- An onto map to one simple factor reads exactly one original coordinate,
followed by an automorphism of that same factor. -/
theorem surjective_factor (f : (I → T) →* T) (hf : Function.Surjective f) :
    ∃ (i : I) (a : MulAut T), ∀ x : I → T, f x = a (x i) := by
  have hker : f.ker ≠ ⊤ := by
    intro h
    have hone : ∀ y : T, y = 1 := by
      intro y
      obtain ⟨x, rfl⟩ := hf y
      exact (show x ∈ f.ker from h ▸ Subgroup.mem_top x)
    obtain ⟨y, hy⟩ := exists_ne (1 : T)
    exact hy (hone y)
  obtain ⟨i, hi⟩ := pi_normal_exists_trivial_coordinate (fun _ : I => T)
    (fun _ => inferInstance) (fun _ => hT) f.ker inferInstance hker
  let a : T →* T := f.comp (MonoidHom.mulSingle (fun _ : I => T) i)
  have hai : Function.Injective a := by
    apply (MonoidHom.ker_eq_bot_iff a).mp
    apply bot_unique
    intro t ht
    change t = 1
    have h := hi (Pi.mulSingle i t) ht
    simpa only [Pi.mulSingle_eq_same] using h
  have has : Function.Surjective a := Finite.surjective_of_injective hai
  refine ⟨i, MulEquiv.ofBijective a ⟨hai, has⟩, ?_⟩
  intro x
  let y := x * (Pi.mulSingle i (x i))⁻¹
  have hy : y i = 1 := by simp only [y, Pi.mul_apply, Pi.inv_apply,
    Pi.mulSingle_eq_same, mul_inv_cancel]
  have hcentral (t : T) : f y * t = t * f y := by
    obtain ⟨u, rfl⟩ := has t
    change f y * f (Pi.mulSingle i u) = f (Pi.mulSingle i u) * f y
    rw [← map_mul, ← map_mul]
    congr 1
    funext j
    by_cases hj : j = i
    · subst j
      simp only [Pi.mul_apply, Pi.mulSingle_eq_same, hy, one_mul, mul_one]
    · simp only [Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, mul_one, one_mul]
  have hfy : f y = 1 := hT (f y) hcentral
  have hsplit : x = y * Pi.mulSingle i (x i) := by simp only [y,
    inv_mul_cancel_right]
  change f x = a (x i)
  calc
    f x = f (y * Pi.mulSingle i (x i)) := congrArg f hsplit
    _ = f (Pi.mulSingle i (x i)) := by rw [map_mul, hfy, one_mul]
    _ = a (x i) := rfl

omit [Fintype I] [Finite T] in
/-- Different original coordinates cannot present the same onto map. -/
theorem coordinate_unique (i j : I) (a b : MulAut T)
    (h : ∀ x : I → T, a (x i) = b (x j)) : i = j := by
  by_contra hij
  obtain ⟨t, ht⟩ := exists_ne (1 : T)
  have he := h (Pi.mulSingle i t)
  simp only [Pi.mulSingle_eq_same,
    Pi.mulSingle_eq_of_ne (Ne.symm hij), map_one] at he
  exact ht (a.injective (he.trans (map_one a).symm))

include hT in
/-- Every automorphism routes the literal simple coordinates by a genuine
permutation and applies one automorphism in each output coordinate. -/
theorem automorphism_coordinates (e : MulAut (I → T)) :
    ∃ (q : Equiv.Perm I) (a : I → MulAut T),
      ∀ (x : I → T) (i : I), e x i = a i (x (q.symm i)) := by
  have honto (i : I) : Function.Surjective
      ((Pi.evalMonoidHom (fun _ : I => T) i).comp e.toMonoidHom) := by
    intro t
    obtain ⟨x, hx⟩ := e.surjective (Pi.mulSingle i t)
    refine ⟨x, ?_⟩
    change e x i = t
    rw [hx, Pi.mulSingle_eq_same]
  choose r a ha using fun i => surjective_factor hT
    ((Pi.evalMonoidHom (fun _ : I => T) i).comp e.toMonoidHom) (honto i)
  have hroute : Function.Surjective r := by
    intro j
    by_contra hn
    push Not at hn
    obtain ⟨t, ht⟩ := exists_ne (1 : T)
    have he : e (Pi.mulSingle j t) = 1 := by
      funext i
      have hi := ha i (Pi.mulSingle j t)
      change e (Pi.mulSingle j t) i =
        a i ((Pi.mulSingle j t : I → T) (r i)) at hi
      simpa only [Pi.mulSingle_eq_of_ne (hn i), map_one] using hi
    have hx : Pi.mulSingle j t = (1 : I → T) :=
      e.injective (he.trans e.map_one.symm)
    exact ht (by simpa only [Pi.mulSingle_eq_same, Pi.one_apply] using congrFun hx j)
  let q : Equiv.Perm I :=
    (Equiv.ofBijective r ⟨Finite.injective_iff_surjective.mpr hroute, hroute⟩).symm
  exact ⟨q, a, fun x i => ha i x⟩

end SymmetricSubgroupAsymptotics.SimpleProductAutomorphismCoordinates
