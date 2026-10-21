import SymmetricSubgroupAsymptotics.CFSGIntravariantFrattini
import Mathlib.GroupTheory.Solvable

/-!
# The normalizer-supplement generation step

This is the group-theoretic fusion step in the induction for soluble
generation. Every subgroup is kept in its original ambient group. A subgroup
of the normalizer that contains the retained subgroup, and two conjugates of
which generate that normalizer, fuses with the two-conjugate generation of
the retained normal subgroup. No simplicity or classification is used here.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGReduction

theorem conjugate_le_of_mem {G : Type*} [Group G]
    {H K : Subgroup G} {x : G} (hx : x ∈ K) (hH : H ≤ K) :
    H.map (MulAut.conj x).toMonoidHom ≤ K := by
  rintro z ⟨h, hh, rfl⟩
  exact K.mul_mem (K.mul_mem hx (hH hh)) (K.inv_mem hx)

/-- The conjugating element is `x * y` because `MulAut.conj` uses left
conjugation. All containment statements refer to the displayed subgroups. -/
theorem two_conjugates_generate_of_normalizer_supplement
    {G : Type*} [Group G] (E H S : Subgroup G) (x y : G)
    (hHS : H ≤ S) (hx : x ∈ E) (hy : y ∈ Subgroup.normalizer H)
    (hE : Subgroup.closure ((H : Set G) ∪
      H.map (MulAut.conj x).toMonoidHom) = E)
    (hN : Subgroup.closure ((S : Set G) ∪
      S.map (MulAut.conj y).toMonoidHom) = Subgroup.normalizer H)
    (hcover : E ⊔ Subgroup.normalizer H = ⊤) :
    Subgroup.closure ((S : Set G) ∪
      S.map (MulAut.conj (x * y)).toMonoidHom) = ⊤ := by
  let K := Subgroup.closure ((S : Set G) ∪
    S.map (MulAut.conj (x * y)).toMonoidHom)
  have hS : S ≤ K := fun _ hs => Subgroup.subset_closure (Or.inl hs)
  have hSxy : S.map (MulAut.conj (x * y)).toMonoidHom ≤ K :=
    fun _ hs => Subgroup.subset_closure (Or.inr hs)
  have hHy : H.map (MulAut.conj y).toMonoidHom = H := by
    apply SetLike.coe_injective
    exact Subgroup.mem_normalizer_iff_conj_image_eq.mp hy
  have hHx : H.map (MulAut.conj x).toMonoidHom ≤ K := by
    rintro z ⟨h, hh, rfl⟩
    have hyh : (MulAut.conj y).symm h ∈ H := by
      exact Subgroup.mem_map_equiv.mp (hHy.symm ▸ hh)
    have hz := hSxy (Subgroup.mem_map.mpr
      ⟨(MulAut.conj y).symm h, hHS hyh, rfl⟩)
    simpa [MulAut.conj_apply, MulAut.conj_symm_apply, mul_assoc] using hz
  have hEK : E ≤ K := by
    rw [← hE]
    exact (Subgroup.closure_le K).mpr (Set.union_subset (hHS.trans hS) hHx)
  have hxK : x ∈ K := hEK hx
  have hSy : S.map (MulAut.conj y).toMonoidHom ≤ K := by
    rintro z ⟨s, hs, rfl⟩
    have hz := hSxy (Subgroup.mem_map.mpr ⟨s, hs, rfl⟩)
    have hz' := K.mul_mem
      (K.mul_mem (K.inv_mem hxK) hz) hxK
    simpa [MulAut.conj_apply, mul_assoc] using hz'
  have hNK : Subgroup.normalizer H ≤ K := by
    rw [← hN]
    exact (Subgroup.closure_le K).mpr (Set.union_subset hS hSy)
  apply top_unique
  rw [← hcover]
  exact sup_le hEK hNK

/-- Intravariance supplies the normalizer supplement automatically. This
form retains the actual subtype embedding of the normal subgroup. -/
theorem two_conjugates_generate_of_normal_intravariant
    {G : Type*} [Group G] (E : Subgroup G) [E.Normal]
    (H : Subgroup E) (S : Subgroup G) (x : E) (y : G)
    (hInv : Intravariant H) (hHS : H.map E.subtype ≤ S)
    (hy : y ∈ Subgroup.normalizer (H.map E.subtype))
    (hE : Subgroup.closure (((H.map E.subtype) : Set G) ∪
      (H.map E.subtype).map (MulAut.conj (x : G)).toMonoidHom) = E)
    (hN : Subgroup.closure ((S : Set G) ∪
      S.map (MulAut.conj y).toMonoidHom) =
        Subgroup.normalizer (H.map E.subtype)) :
    Subgroup.closure ((S : Set G) ∪
      S.map (MulAut.conj ((x : G) * y)).toMonoidHom) = ⊤ := by
  apply two_conjugates_generate_of_normalizer_supplement E (H.map E.subtype) S
    x y hHS x.property hy hE hN
  rw [sup_comm]
  exact normalizer_map_subtype_sup_eq_top E H hInv

end SymmetricSubgroupAsymptotics.CFSGReduction
