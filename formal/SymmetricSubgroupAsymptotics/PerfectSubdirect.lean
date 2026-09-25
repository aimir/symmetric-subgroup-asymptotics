import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Algebra.Group.Pi.Basic

/-! Actual subdirect products of finitely many perfect simple factors
are perfect. The proof uses original coordinate maps and their joint
injectivity. It does not assert the false analogous claim for arbitrary
perfect factors. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem perfect_of_surjective_perfect_kernel {G Q : Type*} [Group G] [Group Q]
    (f : G→*Q) (hf : Function.Surjective f)
    [Group.IsPerfect Q] [Group.IsPerfect f.ker] : Group.IsPerfect G := by
  have hk : f.ker≤commutator G := by
    rw [←Subgroup.commutator_eq_self (H := f.ker)]
    exact Subgroup.commutator_mono le_top le_top
  have hm : (commutator G).map f=⊤ := by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr hf]
    exact Group.IsPerfect.commutator_eq_top
  have hc := congrArg (Subgroup.comap f) hm
  rw [Subgroup.comap_map_eq,Subgroup.comap_top,sup_eq_left.mpr hk] at hc
  exact ⟨hc⟩

theorem perfect_of_perfect_projection_simple_kernel
    {G A B : Type*} [Group G] [Group A] [Group B]
    [Group.IsPerfect A] [IsSimpleGroup B] [Group.IsPerfect B]
    (f : G→*A) (g : G→*B) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hker : Function.Injective (g.comp f.ker.subtype)) : Group.IsPerfect G := by
  let K := f.ker.map g
  letI : K.Normal := Subgroup.Normal.map inferInstance g hg
  have hK : Group.IsPerfect K := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (H := K) inferInstance with h|h
    · rw [h]; infer_instance
    · rw [h]; infer_instance
  let e := MonoidHom.ofInjective hker
  have hr : (g.comp f.ker.subtype).range=K := by
    rw [MonoidHom.range_comp,Subgroup.range_subtype]
  letI : Group.IsPerfect (g.comp f.ker.subtype).range := hr.symm ▸ hK
  letI : Group.IsPerfect f.ker := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact perfect_of_surjective_perfect_kernel f hf

universe u

/-- Every actual source with onto simple coordinates that jointly
separate its elements is perfect. No independence of coordinates is
assumed, and every proper subdirect relation remains allowed. -/
theorem perfect_of_subdirect_fin :
    ∀ (n : ℕ) (S : Fin n→Type u) [∀i,Group (S i)]
      [∀i,IsSimpleGroup (S i)] [∀i,Group.IsPerfect (S i)]
      (G : Type u) [Group G] (f : ∀i,G→*S i),
      (∀i,Function.Surjective (f i)) →
      Function.Injective (fun x i=>f i x) → Group.IsPerfect G := by
  intro n
  induction n with
  | zero =>
    intro S _ _ _ G _ f _ hi
    letI : Subsingleton G := ⟨fun x y=>hi (funext (fun i=>Fin.elim0 i))⟩
    infer_instance
  | succ n ih =>
    intro S _ _ _ G _ f hs hi
    let d : G→*(∀i:Fin n,S i.succ) := {
      toFun := fun x i=>f i.succ x
      map_one' := by funext i; exact (f i.succ).map_one
      map_mul' x y := by funext i; exact (f i.succ).map_mul x y }
    let r (i : Fin n) : d.range→*S i.succ := {
      toFun := fun x=>x.val i
      map_one' := rfl
      map_mul' _ _ := rfl }
    have hr (i : Fin n) : Function.Surjective (r i) := by
      intro y
      obtain ⟨x,hx⟩ := hs i.succ y
      exact ⟨d.rangeRestrict x,hx⟩
    have hir : Function.Injective (fun x i=>r i x) := by
      intro x y he
      apply Subtype.ext
      exact he
    letI : Group.IsPerfect d.range := ih (fun i=>S i.succ) d.range r hr hir
    apply perfect_of_perfect_projection_simple_kernel d.rangeRestrict (f 0)
      d.rangeRestrict_surjective (hs 0)
    intro x y hxy
    apply Subtype.ext
    apply hi
    funext i
    refine Fin.cases ?_ (fun j=>?_) i
    · exact hxy
    · have hx : d x.val=1 := congrArg Subtype.val x.property
      have hy : d y.val=1 := congrArg Subtype.val y.property
      exact congrFun (hx.trans hy.symm) j


theorem simple_perfect_of_nonabelian {G : Type*} [Group G] [IsSimpleGroup G]
    (hG : ¬IsMulCommutative G) : Group.IsPerfect G := by
  rcases Subgroup.Normal.eq_bot_or_eq_top (H := commutator G) inferInstance with h|h
  · exact False.elim (hG ((commutator_eq_bot_iff G).mp h))
  · exact ⟨h⟩

/-- Arbitrary finite coordinate sets, retaining their actual maps. -/
theorem perfect_of_subdirect {ι : Type*} [Fintype ι]
    (S : ι→Type u) [∀i,Group (S i)] [∀i,IsSimpleGroup (S i)]
    [∀i,Group.IsPerfect (S i)] (G : Type u) [Group G] (f : ∀i,G→*S i)
    (hs : ∀i,Function.Surjective (f i))
    (hi : Function.Injective (fun x i=>f i x)) : Group.IsPerfect G := by
  let e := Fintype.equivFin ι
  apply perfect_of_subdirect_fin (Fintype.card ι) (fun j=>S (e.symm j)) G
    (fun j=>f (e.symm j)) (fun j=>hs (e.symm j))
  intro x y h
  apply hi
  funext i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  exact congrFun h j

theorem nonabelian_simple_subdirect_perfect {ι : Type*} [Fintype ι]
    (S : ι→Type u) [∀i,Group (S i)] [∀i,IsSimpleGroup (S i)]
    (hS : ∀i,¬IsMulCommutative (S i))
    (G : Type u) [Group G] (f : ∀i,G→*S i)
    (hs : ∀i,Function.Surjective (f i))
    (hi : Function.Injective (fun x i=>f i x)) : Group.IsPerfect G := by
  letI (i : ι) : Group.IsPerfect (S i) := simple_perfect_of_nonabelian (hS i)
  exact perfect_of_subdirect S G f hs hi

end SymmetricSubgroupAsymptotics
