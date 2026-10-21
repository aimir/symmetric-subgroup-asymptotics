import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrime
import Mathlib.Algebra.Group.Subgroup.Finite

/-! Actual products preserve soluble self-normalizing subgroups and
generation by two conjugates. Coordinate routing is kept explicit for
the subsequent intravariance step. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGReduction

variable {I : Type*} (S : I → Type*) [∀ i, Group (S i)]

theorem conjugate_mulSingle (g : ∀ i, S i) (i : I) (t : S i) :
    g * Pi.mulSingle i t * g⁻¹ = Pi.mulSingle i (g i * t * (g i)⁻¹) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same]
  · simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_of_ne hji,
      mul_one, mul_inv_cancel]

theorem map_pi_of_routing (H : ∀ i, Subgroup (S i)) (e : MulAut (∀ i, S i))
    (r : I → I) (hr : Function.Surjective r) (a : ∀ i, S (r i) ≃* S i)
    (hcoord : ∀ x i, e x i = a i (x (r i))) :
    (Subgroup.pi Set.univ H).map e.toMonoidHom =
      Subgroup.pi Set.univ (fun i => (H (r i)).map (a i).toMonoidHom) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ i _
    exact ⟨x (r i), hx (r i) (Set.mem_univ _), (hcoord x i).symm⟩
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    intro j _
    obtain ⟨i, rfl⟩ := hr j
    obtain ⟨z, hz, hzy⟩ := hy i (Set.mem_univ _)
    have he : a i ((e.symm y) (r i)) = y i :=
      (hcoord (e.symm y) i).symm.trans (congrFun (e.apply_symm_apply y) i)
    have hx : (e.symm y) (r i) = z := (a i).injective (he.trans hzy.symm)
    rw [hx]
    exact hz

theorem normalizer_pi (H : ∀ i, Subgroup (S i)) :
    Subgroup.normalizer (Subgroup.pi Set.univ H : Set (∀ i, S i)) =
      Subgroup.pi Set.univ (fun i => Subgroup.normalizer (H i : Set (S i))) := by
  ext g
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_pi]
  constructor
  · intro hg i _
    apply Subgroup.mem_normalizer_iff.mpr
    intro t
    have h := hg (Pi.mulSingle i t)
    rw [conjugate_mulSingle, Subgroup.mulSingle_mem_pi, Subgroup.mulSingle_mem_pi] at h
    simpa only [Set.mem_univ, true_imp_iff] using h
  · intro hg x
    constructor
    · intro hx i _
      exact (Subgroup.mem_normalizer_iff.mp (hg i (Set.mem_univ _)) (x i)).mp
        (hx i (Set.mem_univ _))
    · intro hx i _
      exact (Subgroup.mem_normalizer_iff.mp (hg i (Set.mem_univ _)) (x i)).mpr
        (hx i (Set.mem_univ _))

theorem product_self_normalizing (H : ∀ i, Subgroup (S i))
    (hH : ∀ i, Subgroup.normalizer (H i : Set (S i)) = H i) :
    Subgroup.normalizer (Subgroup.pi Set.univ H : Set (∀ i, S i)) =
      Subgroup.pi Set.univ H := by
  rw [normalizer_pi]
  congr 1
  funext i
  exact hH i

theorem finite_product_soluble [Fintype I] (H : ∀ i, Subgroup (S i))
    (hH : ∀ i, IsSolvable (H i)) : IsSolvable (Subgroup.pi Set.univ H) := by
  letI productSoluble_factor (i : I) : IsSolvable (H i) := hH i
  choose n hn using fun i => IsSolvable.solvable (G := H i)
  have hp : IsSolvable (∀ i, H i) := by
    refine ⟨∑ i : I, n i, le_antisymm ?_ bot_le⟩
    intro x hx
    apply Subgroup.mem_bot.mpr
    funext i
    have hm := map_derivedSeries_le_derivedSeries (Pi.evalMonoidHom (fun i => H i) i)
      (∑ j : I, n j) ⟨x, hx, rfl⟩
    have hni : n i ≤ ∑ j : I, n j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
    have hh := derivedSeries_antitone (H i) hni hm
    rw [hn i] at hh
    exact Subgroup.mem_bot.mp hh
  letI productSoluble_pi : IsSolvable (∀ i, H i) := hp
  let f : Subgroup.pi Set.univ H →* ∀ i, H i :=
    { toFun := fun x i => ⟨x.val i, x.property i (Set.mem_univ _)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  apply solvable_of_solvable_injective (f := f)
  intro x y h
  apply Subtype.ext
  funext i
  exact congrArg (fun z : H i => (z : S i)) (congrFun h i)

theorem product_two_conjugates_generate [Fintype I] (H : ∀ i, Subgroup (S i))
    (g : ∀ i, S i)
    (hgen : ∀ i, Subgroup.closure ((H i : Set (S i)) ∪
      (H i).map (MulAut.conj (g i)).toMonoidHom) = ⊤) :
    Subgroup.closure (((Subgroup.pi Set.univ H) : Set (∀ i, S i)) ∪
      (Subgroup.pi Set.univ H).map (MulAut.conj g).toMonoidHom) = ⊤ := by
  let K := Subgroup.closure (((Subgroup.pi Set.univ H) : Set (∀ i, S i)) ∪
    (Subgroup.pi Set.univ H).map (MulAut.conj g).toMonoidHom)
  have hsingle (i : I) : (⊤ : Subgroup (S i)) ≤ K.comap (MonoidHom.mulSingle S i) := by
    rw [← hgen i]
    apply (Subgroup.closure_le _).mpr
    apply Set.union_subset
    · intro t ht
      exact Subgroup.subset_closure (Or.inl
        ((Subgroup.mulSingle_mem_pi i t).mpr (fun _ => ht)))
    · rintro _ ⟨t, ht, rfl⟩
      apply Subgroup.subset_closure
      right
      refine ⟨Pi.mulSingle i t,
        (Subgroup.mulSingle_mem_pi i t).mpr (fun _ => ht), ?_⟩
      exact conjugate_mulSingle S g i t
  apply top_unique
  intro x _
  exact Subgroup.pi_mem_of_mulSingle_mem x
    (fun i => hsingle i (Subgroup.mem_top _))

end SymmetricSubgroupAsymptotics.CFSGReduction
