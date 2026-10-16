import Mathlib.GroupTheory.Sylow

/-! Lift an element of the normalizer of the literal Sylow image to the
normalizer of the actual original Sylow subgroup. The proof uses Frattini
inside the exact preimage normalizer; no complement or splitting is chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.SylowActualNormalizerLift

theorem exists_lift {G H : Type*} [Group G] [Finite G] [Group H]
    {p : ℕ} [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (P : Sylow p G) (h : H)
    (hh : h ∈ Subgroup.normalizer ((P : Subgroup G).map f : Set H)) :
    ∃ g : G, g ∈ Subgroup.normalizer (P : Set G) ∧ f g = h := by
  let Q := (P : Subgroup G).map f
  let M := (Subgroup.normalizer (Q : Set H)).comap f
  let N := Q.comap f
  have hPM : (P : Subgroup G) ≤ M := by
    intro x hx
    change f x ∈ Subgroup.normalizer (Q : Set H)
    exact Q.le_normalizer ⟨x,hx,rfl⟩
  let PS : Sylow p M := P.subtype hPM
  let NM := N.subgroupOf M
  letI : NM.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (Q.le_normalizer_comap f)
  have hPS : (PS : Subgroup M) ≤ NM := by
    intro x hx
    change (x : G) ∈ (P : Subgroup G) at hx
    change f (x : G) ∈ Q
    exact ⟨x,hx,rfl⟩
  let fm : M →* Subgroup.normalizer (Q : Set H) :=
    { toFun := fun x => ⟨f x.1,x.2⟩
      map_one' := Subtype.ext f.map_one
      map_mul' := fun x y => Subtype.ext (f.map_mul x.1 y.1) }
  have hfm : Function.Surjective fm := by
    intro y
    obtain ⟨x,hx⟩ := hf y.1
    refine ⟨⟨x,?_⟩,?_⟩
    · change f x ∈ Subgroup.normalizer (Q : Set H)
      rw [hx]
      exact y.2
    · exact Subtype.ext hx
  have himage : NM.map fm = (PS : Subgroup M).map fm := by
    apply le_antisymm
    · rintro y ⟨n,hn,rfl⟩
      change f (n : G) ∈ Q at hn
      obtain ⟨x,hx,heq⟩ := hn
      refine ⟨⟨x,hPM hx⟩,?_,Subtype.ext heq⟩
      change x ∈ (P : Subgroup G)
      exact hx
    · exact Subgroup.map_mono hPS
  have hle : NM.map fm ≤ (Subgroup.normalizer (PS : Set M)).map fm := by
    rw [himage]
    exact Subgroup.map_mono (PS : Subgroup M).le_normalizer
  have hwhole := congrArg (fun K : Subgroup M => K.map fm)
    (Sylow.normalizer_sup_eq_top' PS hPS)
  change (Subgroup.normalizer (PS : Set M) ⊔ NM).map fm =
    (⊤ : Subgroup M).map fm at hwhole
  rw [Subgroup.map_sup,Subgroup.map_top_of_surjective fm hfm,
    sup_eq_left.mpr hle] at hwhole
  have hm : (⟨h,hh⟩ : Subgroup.normalizer (Q : Set H)) ∈
      (Subgroup.normalizer (PS : Set M)).map fm := by
    rw [hwhole]
    trivial
  obtain ⟨g,hg,heq⟩ := hm
  have hPSmap : (PS : Subgroup M).map M.subtype = (P : Subgroup G) := by
    change ((P : Subgroup G).subgroupOf M).map M.subtype = (P : Subgroup G)
    rw [Subgroup.subgroupOf_map_subtype,inf_of_le_left hPM]
  have hgn := ((PS : Subgroup M).le_normalizer_map M.subtype)
    (show (g : G) ∈ (Subgroup.normalizer (PS : Set M)).map M.subtype from ⟨g,hg,rfl⟩)
  rw [hPSmap] at hgn
  exact ⟨g.1,hgn,congrArg Subtype.val heq⟩

end SymmetricSubgroupAsymptotics.SylowActualNormalizerLift
