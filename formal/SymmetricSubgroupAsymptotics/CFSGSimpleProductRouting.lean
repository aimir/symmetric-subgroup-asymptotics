import SymmetricSubgroupAsymptotics.SemisimpleOuterFibre

/-! An automorphism of an actual finite product of nonabelian simple
groups routes the original factors through actual factor isomorphisms.
The factors need not all have the same isomorphism type. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReduction

theorem onto_simple_factor {I : Type*} [Fintype I]
    (S : I → Type*) [∀ i, Group (S i)]
    (hsimple : ∀ i, IsSimpleGroup (S i)) (hZ : ∀ i, IsCenterless (S i))
    {T : Type*} [Group T] [IsSimpleGroup T]
    (f : (∀ i, S i) →* T) (hf : Function.Surjective f) :
    ∃ (i : I) (a : S i ≃* T), ∀ x, f x = a (x i) := by
  have hker : f.ker ≠ ⊤ := by
    intro ht
    obtain ⟨t, ht1⟩ := exists_ne (1 : T)
    obtain ⟨x, rfl⟩ := hf t
    have hx : x ∈ f.ker := by rw [ht]; exact Subgroup.mem_top x
    exact ht1 (MonoidHom.mem_ker.mp hx)
  obtain ⟨i, hi⟩ := pi_normal_exists_trivial_coordinate S hsimple hZ f.ker inferInstance hker
  let K := (Pi.evalMonoidHom S i).ker
  have hle : f.ker ≤ K := hi
  have hKne : K ≠ ⊤ := by
    intro ht
    letI simpleProductRouting_factor : IsSimpleGroup (S i) := hsimple i
    obtain ⟨t, ht1⟩ := exists_ne (1 : S i)
    have h : Pi.mulSingle i t ∈ K := ht ▸ Subgroup.mem_top _
    change (Pi.mulSingle i t : ∀ j, S j) i = 1 at h
    exact ht1 (by simpa only [Pi.mulSingle_eq_same] using h)
  have hnormal : (K.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hback : K ≤ f.ker := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map f) hnormal with hb | ht
    · intro x hx
      have h : f x ∈ K.map f := ⟨x, hx, rfl⟩
      rw [hb, Subgroup.mem_bot] at h
      exact h
    · have heq : (K.map f).comap f = K := Subgroup.comap_map_eq_self hle
      rw [ht, Subgroup.comap_top] at heq
      exact False.elim (hKne heq.symm)
  let a : S i →* T := f.comp (MonoidHom.mulSingle S i)
  have hai : Function.Injective a := by
    apply (MonoidHom.ker_eq_bot_iff a).mp
    apply bot_unique
    intro t ht
    change t = 1
    have h := hi (Pi.mulSingle i t) ht
    simpa only [Pi.mulSingle_eq_same] using h
  have hfactor (x : ∀ i, S i) : f x = a (x i) := by
    let y := x * (Pi.mulSingle i (x i))⁻¹
    have hy : y ∈ K := by
      change y i = 1
      simp only [y, Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same, mul_inv_cancel]
    have hfy : f y = 1 := hback hy
    have hx : x = y * Pi.mulSingle i (x i) := by
      simp only [y, inv_mul_cancel_right]
    calc
      f x = f (y * Pi.mulSingle i (x i)) := congrArg f hx
      _ = f (Pi.mulSingle i (x i)) := by rw [map_mul, hfy, one_mul]
      _ = a (x i) := rfl
  have has : Function.Surjective a := by
    intro t
    obtain ⟨x, rfl⟩ := hf t
    exact ⟨x i, (hfactor x).symm⟩
  exact ⟨i, MulEquiv.ofBijective a ⟨hai, has⟩, hfactor⟩

theorem simple_product_automorphism_routing {I : Type*} [Fintype I]
    (S : I → Type*) [∀ i, Group (S i)]
    (hsimple : ∀ i, IsSimpleGroup (S i)) (hZ : ∀ i, IsCenterless (S i))
    (e : MulAut (∀ i, S i)) :
    ∃ r : I → I, Function.Bijective r ∧
      ∃ a : ∀ i, S (r i) ≃* S i, ∀ x i, e x i = a i (x (r i)) := by
  have honto (i : I) : Function.Surjective ((Pi.evalMonoidHom S i).comp e.toMonoidHom) := by
    intro t
    obtain ⟨x, hx⟩ := e.surjective (Pi.mulSingle i t)
    refine ⟨x, ?_⟩
    change e x i = t
    rw [hx, Pi.mulSingle_eq_same]
  have hf (i : I) : ∃ j : I, ∃ a : S j ≃* S i,
      ∀ x, e x i = a (x j) := by
    letI simpleProductRouting_target : IsSimpleGroup (S i) := hsimple i
    exact onto_simple_factor S hsimple hZ _ (honto i)
  choose r a ha using hf
  have hr : Function.Surjective r := by
    intro j
    by_contra hn
    push Not at hn
    letI simpleProductRouting_source : IsSimpleGroup (S j) := hsimple j
    obtain ⟨t, ht⟩ := exists_ne (1 : S j)
    have he : e (Pi.mulSingle j t) = 1 := by
      funext i
      have h := ha i (Pi.mulSingle j t)
      simpa only [Pi.mulSingle_eq_of_ne (hn i), map_one] using h
    have hx : Pi.mulSingle j t = (1 : ∀ i, S i) :=
      e.injective (he.trans e.map_one.symm)
    exact ht (by simpa only [Pi.mulSingle_eq_same, Pi.one_apply] using congrFun hx j)
  exact ⟨r, ⟨Finite.injective_iff_surjective.mpr hr, hr⟩, a, fun x i => ha i x⟩

end SymmetricSubgroupAsymptotics.CFSGReduction
