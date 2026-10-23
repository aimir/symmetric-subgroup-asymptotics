import SymmetricSubgroupAsymptotics.CFSGConjugateComap
import SymmetricSubgroupAsymptotics.CFSGRangeFactorCardinality

/-! Finite conjugate-family counts through actual group maps, subgroup
inclusions and preimages. These bounds need no representation faithfulness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGConjugateFamilyTransport
open CFSGSubgroupConjugateRestriction CFSGRangeFactorCardinality CFSGConjugateComap

private def finiteRange {A B : Type*} [Finite A] (f : A → B) : Finite (Set.range f) :=
  Finite.of_surjective (Set.rangeFactorization f) Set.rangeFactorization_surjective

theorem card_family_map_le {G Q : Type*} [Group G] [Group Q] [Finite G]
    (f : G →* Q) (hf : Function.Surjective f) (R : Subgroup G) :
    Nat.card (Set.range (fun q : Q => (R.map f).map (MulAut.conj q).toMonoidHom)) ≤
      Nat.card (Set.range (fun g : G => R.map (MulAut.conj g).toMonoidHom)) := by
  let F (g : G) := R.map (MulAut.conj g).toMonoidHom
  letI : Finite (Set.range F) := finiteRange F
  let T (g : G) := (R.map f).map (MulAut.conj (f g)).toMonoidHom
  have hfactor : ∀ g h, F g = F h → T g = T h := by
    intro g h he
    have hh := congrArg (fun S : Subgroup G => S.map f) he
    simpa only [F,T,map_conjugate] using hh
  have hr : Set.range T = Set.range (fun q : Q =>
      (R.map f).map (MulAut.conj q).toMonoidHom) :=
    hf.range_comp (fun q : Q => (R.map f).map (MulAut.conj q).toMonoidHom)
  rw [←hr]
  exact card_range_le_of_factor F T hfactor

theorem card_subgroup_family_le {G : Type*} [Group G]
    (H : Subgroup G) [Finite H] (R : Subgroup H) :
    Nat.card (Set.range (fun g : H => R.map (MulAut.conj g).toMonoidHom)) ≤
      Nat.card (Set.range (fun g : H => (R.map H.subtype).map
        (MulAut.conj g.val).toMonoidHom)) := by
  let F (g : H) := (R.map H.subtype).map (MulAut.conj g.val).toMonoidHom
  letI : Finite (Set.range F) := finiteRange F
  let T (g : H) := R.map (MulAut.conj g).toMonoidHom
  apply card_range_le_of_factor F T
  intro g h he
  apply Subgroup.map_injective H.subtype_injective
  simpa only [F,T,map_conjugate] using he

theorem card_family_le_of_range {A G : Type*} [Group A] [Group G] [Finite A]
    (f : A →* G) (H R : Subgroup G) (hH : H ≤ f.range) :
    Nat.card (Set.range (fun h : H => R.map (MulAut.conj h.val).toMonoidHom)) ≤
      Nat.card (Set.range (fun a : A => R.map (MulAut.conj (f a)).toMonoidHom)) := by
  letI : Finite (Set.range (fun a : A => R.map (MulAut.conj (f a)).toMonoidHom)) :=
    finiteRange _
  have hcover (x : Set.range (fun h : H => R.map (MulAut.conj h.val).toMonoidHom)) :
      x.val ∈ Set.range (fun a : A => R.map (MulAut.conj (f a)).toMonoidHom) := by
    obtain ⟨h,hh⟩ := x.property
    obtain ⟨a,ha⟩ := hH h.property
    exact ⟨a,(congrArg (fun g : G => R.map (MulAut.conj g).toMonoidHom) ha).trans hh⟩
  let enc (x : Set.range (fun h : H => R.map (MulAut.conj h.val).toMonoidHom)) :
      Set.range (fun a : A => R.map (MulAut.conj (f a)).toMonoidHom) := ⟨x.val,hcover x⟩
  apply Nat.card_le_card_of_injective enc
  intro x y he
  apply Subtype.ext
  exact congrArg (fun z : Set.range (fun a : A =>
    R.map (MulAut.conj (f a)).toMonoidHom) => z.val) he

theorem card_comap_image_family_le {G H Q : Type*} [Group G] [Group H] [Group Q]
    [Finite G] (rho : G →* H) (f : G →* Q) (R : Subgroup H) :
    Nat.card (Set.range (fun g : G => ((R.comap rho).map f).map
      (MulAut.conj (f g)).toMonoidHom)) ≤
    Nat.card (Set.range (fun g : G => R.map (MulAut.conj (rho g)).toMonoidHom)) := by
  let F (g : G) := R.map (MulAut.conj (rho g)).toMonoidHom
  letI : Finite (Set.range F) := finiteRange F
  let T (g : G) := ((R.comap rho).map f).map (MulAut.conj (f g)).toMonoidHom
  apply card_range_le_of_factor F T
  intro g h he
  have hh := conjugate_comap_eq_of_conjugate_eq rho R g h he
  have hh' := congrArg (fun S : Subgroup G => S.map f) hh
  simpa only [T,map_conjugate] using hh'

end SymmetricSubgroupAsymptotics.CFSGConjugateFamilyTransport
