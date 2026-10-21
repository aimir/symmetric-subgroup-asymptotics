import SymmetricSubgroupAsymptotics.CFSGSolubleGenerationQuotients
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.SetLike.Fintype
import Mathlib.Order.Preorder.Finite

/-!
# The actual soluble radical

Finite joins of soluble normal subgroups are soluble by an elementary
quotient argument. A maximal such subgroup is therefore the largest one,
is characteristic, and has radical-free quotient. This provides the radical
step of the soluble-generation induction without a structural hypothesis.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGReduction

theorem soluble_subgroup_map {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (M : Subgroup G) [IsSolvable M] : IsSolvable (M.map f) := by
  let g : M →* M.map f :=
    { toFun := fun x => ⟨f x, ⟨x, x.property, rfl⟩⟩
      map_one' := Subtype.ext f.map_one
      map_mul' := fun x y => Subtype.ext (f.map_mul x y) }
  apply solvable_of_surjective (f := g)
  rintro ⟨y, x, hx, he⟩
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

/-- Normality of the first soluble subgroup suffices for the join. -/
theorem soluble_sup_of_normal {G : Type*} [Group G]
    (N M : Subgroup G) [N.Normal] [IsSolvable N] [IsSolvable M] :
    IsSolvable ↥(N ⊔ M) := by
  let q := QuotientGroup.mk' N
  let R := M.map q
  letI : IsSolvable R := soluble_subgroup_map q M
  have hN : N.map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff N).mpr
    rw [QuotientGroup.ker_mk']
  have hsup : (N ⊔ M).map q = R := by
    rw [Subgroup.map_sup, hN, bot_sup_eq]
  let j : N →* ↥(N ⊔ M) := Subgroup.inclusion le_sup_left
  let g : ↥(N ⊔ M) →* R :=
    { toFun := fun x => ⟨q x, by
        rw [← hsup]
        exact ⟨x, x.property, rfl⟩⟩
      map_one' := Subtype.ext q.map_one
      map_mul' := fun x y => Subtype.ext (q.map_mul x y) }
  apply solvable_of_ker_le_range j g
  intro x hx
  have hqx : q (x : G) = 1 :=
    congrArg (fun r : R => (r : G ⧸ N)) (MonoidHom.mem_ker.mp hx)
  have hxN : (x : G) ∈ N := (QuotientGroup.eq_one_iff _).mp hqx
  exact ⟨⟨x, hxN⟩, Subtype.ext rfl⟩

theorem exists_largest_soluble_normal (G : Type*) [Group G] [Finite G] :
    ∃ R : Subgroup G, R.Normal ∧ IsSolvable R ∧
      ∀ N : Subgroup G, N.Normal → IsSolvable N → N ≤ R := by
  classical
  let s : Set (Subgroup G) := {N | N.Normal ∧ IsSolvable N}
  obtain ⟨R, hR, hmax⟩ := s.toFinite.exists_maximal
    (show s.Nonempty from ⟨⊥, inferInstance, inferInstance⟩)
  letI := hR.1
  letI := hR.2
  refine ⟨R, hR.1, hR.2, ?_⟩
  intro N hn hs
  letI := hn
  letI := hs
  have hjoin : R ⊔ N ∈ s :=
    ⟨inferInstance, soluble_sup_of_normal R N⟩
  exact le_sup_right.trans (hmax hjoin le_sup_left)

/-- This definition chooses an actual subgroup; its universal property
below makes it independent of the choice of maximal witness. -/
def solubleRadical (G : Type*) [Group G] [Finite G] : Subgroup G :=
  Classical.choose (exists_largest_soluble_normal G)

instance solubleRadical_normal (G : Type*) [Group G] [Finite G] :
    (solubleRadical G).Normal :=
  (Classical.choose_spec (exists_largest_soluble_normal G)).1

instance solubleRadical_soluble (G : Type*) [Group G] [Finite G] :
    IsSolvable (solubleRadical G) :=
  (Classical.choose_spec (exists_largest_soluble_normal G)).2.1

theorem le_solubleRadical {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] [IsSolvable N] : N ≤ solubleRadical G :=
  (Classical.choose_spec (exists_largest_soluble_normal G)).2.2 N
    inferInstance inferInstance

instance solubleRadical_characteristic (G : Type*) [Group G] [Finite G] :
    (solubleRadical G).Characteristic := by
  apply Subgroup.characteristic_iff_map_le.mpr
  intro a
  letI : ((solubleRadical G).map a.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance a.toMonoidHom a.surjective
  letI : IsSolvable ((solubleRadical G).map a.toMonoidHom) :=
    soluble_subgroup_map a.toMonoidHom (solubleRadical G)
  exact le_solubleRadical _

/-- Every soluble normal subgroup in the actual radical quotient is
trivial. Both the kernel and the inverse image remain literal subgroups. -/
theorem quotient_soluble_normal_eq_bot {G : Type*} [Group G] [Finite G]
    (N : Subgroup (G ⧸ solubleRadical G)) [N.Normal] [IsSolvable N] : N = ⊥ := by
  let q := QuotientGroup.mk' (solubleRadical G)
  letI : IsSolvable q.ker := by
    change IsSolvable (QuotientGroup.mk' (solubleRadical G)).ker
    rw [QuotientGroup.ker_mk']
    infer_instance
  letI : IsSolvable (N.comap q) := soluble_comap_of_soluble_ker q N
  have h := Subgroup.map_mono (f := q) (le_solubleRadical (N.comap q))
  rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) N] at h
  have hR : (solubleRadical G).map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [QuotientGroup.ker_mk']
  exact le_bot_iff.mp (h.trans_eq hR)

theorem solubleRadical_quotient_eq_bot (G : Type*) [Group G] [Finite G] :
    solubleRadical (G ⧸ solubleRadical G) = ⊥ :=
  quotient_soluble_normal_eq_bot _

end SymmetricSubgroupAsymptotics.CFSGReduction
