import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index

/-! The splitting of one ambient conjugacy class inside a normal
subgroup is bounded by the index of the subgroup joined with the actual
centralizer. This retains more information than the whole subgroup
index and can charge scalar centralizers in matrix groups. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NormalSubgroupConjugacyFibre
variable {G : Type*} [Group G] (H : Subgroup G) [H.Normal]

instance normalClassConjugation : MulAction G (ConjClasses H) where
  smul g c := ConjClasses.map (MulAut.conjNormal g).toMonoidHom c
  one_smul c := by
    obtain ⟨x,rfl⟩ := ConjClasses.mk_surjective c
    change ConjClasses.mk (MulAut.conjNormal (1:G) x) = ConjClasses.mk x
    rw [map_one]
    rfl
  mul_smul g h c := by
    obtain ⟨x,rfl⟩ := ConjClasses.mk_surjective c
    change ConjClasses.mk (MulAut.conjNormal (g*h) x) =
      ConjClasses.mk (MulAut.conjNormal g (MulAut.conjNormal h x))
    rw [map_mul]
    rfl

theorem normalClass_smul_mk (g : G) (x : H) :
    g • ConjClasses.mk x = ConjClasses.mk (MulAut.conjNormal g x) := rfl

theorem subgroup_le_class_stabilizer (x : H) :
    H ≤ MulAction.stabilizer G (ConjClasses.mk x) := by
  intro g hg
  let h : H := ⟨g,hg⟩
  change ConjClasses.mk (MulAut.conjNormal g x) = ConjClasses.mk x
  have he : MulAut.conjNormal g x = h*x*h⁻¹ := rfl
  rw [he]
  exact (ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨h,rfl⟩)).symm

theorem centralizer_le_class_stabilizer (x : H) :
    Subgroup.centralizer ({(x:G)} : Set G) ≤ MulAction.stabilizer G (ConjClasses.mk x) := by
  intro g hg
  change ConjClasses.mk (MulAut.conjNormal g x) = ConjClasses.mk x
  have hc : (x:G)*g = g*(x:G) := (Subgroup.mem_centralizer_iff.mp hg) _ rfl
  have he : MulAut.conjNormal g x = x := by
    apply Subtype.ext
    change g*(x:G)*g⁻¹ = (x:G)
    rw [←hc,mul_assoc,mul_inv_cancel,mul_one]
  rw [he]

theorem fibre_card_le_join_centralizer_index [Finite G] (x : H) :
    Nat.card {c : ConjClasses H //
      ConjClasses.map H.subtype c = ConjClasses.mk (x:G)} ≤
      (H ⊔ Subgroup.centralizer ({(x:G)} : Set G)).index := by
  letI : Finite (ConjClasses H) :=
    Finite.of_surjective (ConjClasses.mk : H → ConjClasses H) ConjClasses.mk_surjective
  let f : {c : ConjClasses H // ConjClasses.map H.subtype c = ConjClasses.mk (x:G)} →
      MulAction.orbit G (ConjClasses.mk x) := fun c => ⟨c.val, by
    obtain ⟨y,hy⟩ := ConjClasses.mk_surjective c.val
    have hc := c.property
    rw [←hy] at hc
    change ConjClasses.mk (y:G) = ConjClasses.mk (x:G) at hc
    obtain ⟨g,hg⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hc).symm
    refine ⟨g,?_⟩
    change g • ConjClasses.mk x = c.val
    rw [←hy]
    change ConjClasses.mk (MulAut.conjNormal g x) = ConjClasses.mk y
    apply congrArg ConjClasses.mk
    apply Subtype.ext
    exact hg⟩
  have hf : Function.Injective f := by
    intro c d h
    apply Subtype.ext
    exact congrArg (fun z : MulAction.orbit G (ConjClasses.mk x) => z.val) h
  have hs : H ⊔ Subgroup.centralizer ({(x:G)} : Set G) ≤
      MulAction.stabilizer G (ConjClasses.mk x) :=
    sup_le (subgroup_le_class_stabilizer H x) (centralizer_le_class_stabilizer H x)
  calc
    _ ≤ Nat.card (MulAction.orbit G (ConjClasses.mk x)) := Nat.card_le_card_of_injective f hf
    _ = (MulAction.stabilizer G (ConjClasses.mk x)).index :=
      Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G (ConjClasses.mk x))
    _ ≤ _ := Subgroup.index_antitone hs

end SymmetricSubgroupAsymptotics.NormalSubgroupConjugacyFibre
