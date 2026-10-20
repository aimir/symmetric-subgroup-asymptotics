import SymmetricSubgroupAsymptotics.SylowActualNormalizerLift
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Order.Preorder.Finite

/-! Every finite nilpotent quotient is the image of an actual nilpotent
subgroup of its original source. Minimality and the actual Sylow-normalizer
lift avoid any additional Frattini or splitting hypothesis. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

/-- Choose an actual subgroup minimal among those onto the original
nilpotent target. Every Sylow normalizer is still onto, so minimality makes
all its Sylows normal. Solubility is not needed. -/
theorem exists_nilpotent_subgroup_surjective_nilpotent
    {G A : Type} [Group G] [Finite G] [Group A] [Finite A]
    [Group.IsNilpotent A] (f : G →* A) (hf : Function.Surjective f) :
    ∃ H : Subgroup G, Group.IsNilpotent H ∧
      Function.Surjective (f.comp H.subtype) := by
  let good : Subgroup G → Prop :=
    fun H => Function.Surjective (f.comp H.subtype)
  have htop : good ⊤ := by
    intro a
    obtain ⟨g,hg⟩ := hf a
    exact ⟨⟨g,Subgroup.mem_top g⟩,hg⟩
  obtain ⟨H,_,hmin⟩ := Finite.exists_le_minimal
    (p := good) (a := (⊤ : Subgroup G)) htop
  have hH : Function.Surjective (f.comp H.subtype) := hmin.1
  refine ⟨H,?_,hH⟩
  apply ((Group.isNilpotent_of_finite_tfae (G := H)).out 0 3).mpr
  intro p hp P
  letI : Fact p.Prime := hp
  let Q : Sylow p A := P.mapSurjective hH
  have hall : ∀ (q : ℕ) (_hq : Fact q.Prime) (R : Sylow q A),
      (R : Subgroup A).Normal :=
    ((Group.isNilpotent_of_finite_tfae (G := A)).out 0 3).mp
      (inferInstance : Group.IsNilpotent A)
  have hQ : (Q : Subgroup A).Normal := hall p hp Q
  let N : Subgroup H := Subgroup.normalizer (P : Set H)
  have hNonto : Function.Surjective ((f.comp H.subtype).comp N.subtype) := by
    intro a
    have ha : a∈Subgroup.normalizer
        (((P : Subgroup H).map (f.comp H.subtype)) : Set A) := by
      change a∈Subgroup.normalizer ((Q : Subgroup A) : Set A)
      rw [@Subgroup.normalizer_eq_top A _ (Q : Subgroup A) hQ]
      trivial
    obtain ⟨g,hg,hga⟩ := SylowActualNormalizerLift.exists_lift
      (f.comp H.subtype) hH P a ha
    exact ⟨⟨g,hg⟩,hga⟩
  have hgood : good (N.map H.subtype) := by
    intro a
    obtain ⟨n,hn⟩ := hNonto a
    exact ⟨⟨(n : H),⟨n,n.property,rfl⟩⟩,hn⟩
  have hmap : N.map H.subtype=H :=
    hmin.eq_of_le hgood (Subgroup.map_subtype_le N)
  have hNtop : N=⊤ := by
    apply top_unique
    intro h _
    have hh : (h : G)∈N.map H.subtype := by rw [hmap]; exact h.property
    obtain ⟨n,hn,hnh⟩ := hh
    exact (Subtype.ext hnh : n=h) ▸ hn
  exact Subgroup.normalizer_eq_top_iff.mp hNtop

/-- A literal nilpotent subgroup of an arbitrary finite quotient has a
literal nilpotent subgroup lift in the original ambient group. -/
theorem exists_nilpotent_subgroup_map_eq
    {G Q : Type} [Group G] [Finite G] [Group Q] [Finite Q]
    (f : G →* Q) (hf : Function.Surjective f)
    (K : Subgroup Q) [Group.IsNilpotent K] :
    ∃ H : Subgroup G, Group.IsNilpotent H ∧ H.map f=K := by
  let P : Subgroup G := K.comap f
  let g : P →* K := {
    toFun := fun x => ⟨f x,x.property⟩
    map_one' := Subtype.ext f.map_one
    map_mul' := fun x y => Subtype.ext (f.map_mul x y) }
  have hg : Function.Surjective g := by
    intro k
    obtain ⟨x,hx⟩ := hf k
    exact ⟨⟨x,by change f x∈K; rw [hx]; exact k.property⟩,Subtype.ext hx⟩
  obtain ⟨L,hL,hs⟩ := exists_nilpotent_subgroup_surjective_nilpotent g hg
  let H : Subgroup G := L.map P.subtype
  have hH : Group.IsNilpotent H := by
    letI : Group.IsNilpotent L := hL
    exact Group.nilpotent_of_mulEquiv (L.equivMapOfInjective P.subtype Subtype.val_injective)
  refine ⟨H,hH,?_⟩
  apply le_antisymm
  · rintro q ⟨x,⟨y,hy,rfl⟩,rfl⟩
    exact y.property
  · intro k hk
    obtain ⟨l,hl⟩ := hs ⟨k,hk⟩
    exact ⟨((l : P) : G),⟨(l : P),l.property,rfl⟩,congrArg Subtype.val hl⟩

end SymmetricSubgroupAsymptotics
