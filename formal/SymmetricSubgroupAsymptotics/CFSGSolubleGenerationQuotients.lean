import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Lifting soluble generation through a soluble kernel

The subgroup upstairs is the literal inverse image, and the conjugating
element is any actual lift of the displayed quotient element. These elementary
lemmas supply the quotient step in soluble-generation induction.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGReduction

theorem soluble_comap_of_soluble_ker {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (H : Subgroup Q) [IsSolvable f.ker] [IsSolvable H] :
    IsSolvable (H.comap f) := by
  let j : f.ker →* H.comap f :=
    { toFun := fun x => ⟨x, by
        change f x ∈ H
        rw [show f x = 1 from x.property]
        exact H.one_mem⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let g : H.comap f →* H :=
    { toFun := fun x => ⟨f x, x.property⟩
      map_one' := Subtype.ext f.map_one
      map_mul' := fun x y => Subtype.ext (f.map_mul x y) }
  apply solvable_of_ker_le_range j g
  intro x hx
  have hx' : f (x : G) = 1 :=
    congrArg (fun y : H => (y : Q)) (MonoidHom.mem_ker.mp hx)
  exact ⟨⟨x, hx'⟩, Subtype.ext rfl⟩

/-- The kernel lies in the actual preimage subgroup, so surjectivity of the
generated image suffices for generation upstairs. -/
theorem preimage_two_conjugates_generate {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) (H : Subgroup Q) (g : G)
    (hgen : Subgroup.closure ((H : Set Q) ∪
      H.map (MulAut.conj (f g)).toMonoidHom) = ⊤) :
    Subgroup.closure (((H.comap f) : Set G) ∪
      (H.comap f).map (MulAut.conj g).toMonoidHom) = ⊤ := by
  let K := Subgroup.closure (((H.comap f) : Set G) ∪
    (H.comap f).map (MulAut.conj g).toMonoidHom)
  have hH : H.comap f ≤ K := fun _ hx => Subgroup.subset_closure (Or.inl hx)
  have hCg : (H.comap f).map (MulAut.conj g).toMonoidHom ≤ K :=
    fun _ hx => Subgroup.subset_closure (Or.inr hx)
  have hker : f.ker ≤ K := by
    intro x hx
    apply hH
    change f x ∈ H
    rw [MonoidHom.mem_ker.mp hx]
    exact H.one_mem
  have hHm : H ≤ K.map f := by
    intro x hx
    obtain ⟨y, rfl⟩ := hf x
    exact ⟨y, hH hx, rfl⟩
  have hCm : H.map (MulAut.conj (f g)).toMonoidHom ≤ K.map f := by
    rintro z ⟨q, hq, rfl⟩
    obtain ⟨y, rfl⟩ := hf q
    refine ⟨(MulAut.conj g) y, hCg ⟨y, hq, rfl⟩, ?_⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, f.map_mul, f.map_inv]
  have htop : K.map f = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact (Subgroup.closure_le (K.map f)).mpr (Set.union_subset hHm hCm)
  have heq := Subgroup.comap_map_eq_self hker
  rw [htop, Subgroup.comap_top] at heq
  exact heq.symm

theorem soluble_two_conjugate_generation_lift
    {G Q : Type*} [Group G] [Group Q] (f : G →* Q)
    (hf : Function.Surjective f) [IsSolvable f.ker]
    (H : Subgroup Q) [IsSolvable H] (g : G)
    (hgen : Subgroup.closure ((H : Set Q) ∪
      H.map (MulAut.conj (f g)).toMonoidHom) = ⊤) :
    IsSolvable (H.comap f) ∧ f.ker ≤ H.comap f ∧
      Subgroup.closure (((H.comap f) : Set G) ∪
        (H.comap f).map (MulAut.conj g).toMonoidHom) = ⊤ := by
  refine ⟨soluble_comap_of_soluble_ker f H, ?_,
    preimage_two_conjugates_generate f hf H g hgen⟩
  intro x hx
  change f x ∈ H
  rw [MonoidHom.mem_ker.mp hx]
  exact H.one_mem

end SymmetricSubgroupAsymptotics.CFSGReduction
