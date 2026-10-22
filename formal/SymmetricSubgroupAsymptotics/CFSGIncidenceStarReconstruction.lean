import Mathlib.Data.Set.Function

/-! Reconstructing points from a relation on incident lines. The hypotheses
are local triangle and common-neighbour statements, not an assumed point
action. Concrete polar geometries must prove these statements before using
the theorem; no polar-space classification is imported here. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGIncidenceStarReconstruction
variable {P L : Type*}

structure Geometry (rel : L → L → Prop) where
  incident : P → L → Prop
  symmetric : ∀ {x y}, rel x y → rel y x
  seed : ∀ p, ∃ x y, incident p x ∧ incident p y ∧ rel x y
  edgePoint : ∀ {x y}, rel x y → ∃ p, incident p x ∧ incident p y
  uniquePoint : ∀ {p q x y}, rel x y → incident p x → incident p y →
    incident q x → incident q y → p=q
  triangle : ∀ {p x y z}, incident p x → incident p y → rel x y →
    rel x z → rel y z → incident p z
  bridge : ∀ {p x y t}, incident p x → incident p y → incident p t →
    rel x y → ¬(rel x t ∧ rel y t) →
      ∃ z, incident p z ∧ rel x z ∧ rel y z ∧ rel t z

variable {rel : L → L → Prop} (G : Geometry (P:=P) rel)

theorem map_star_into (f : L → L) (hf : ∀ {x y}, rel x y → rel (f x) (f y))
    {p q : P} {x y : L} (hpx : G.incident p x) (hpy : G.incident p y)
    (hxy : rel x y) (hqx : G.incident q (f x)) (hqy : G.incident q (f y)) :
    ∀ {t}, G.incident p t → G.incident q (f t) := by
  have step : ∀ {a b t}, G.incident p a → G.incident p b → G.incident p t →
      rel a b → G.incident q (f a) → G.incident q (f b) → rel a t →
        G.incident q (f t) := by
    intro a b t hpa hpb hpt hab hqa hqb hat
    by_cases hbt : rel b t
    · exact G.triangle hqa hqb (hf hab) (hf hat) (hf hbt)
    · obtain ⟨z,hpz,haz,hbz,htz⟩ := G.bridge hpa hpb hpt hab (fun h=>hbt h.2)
      have hqz := G.triangle hqa hqb (hf hab) (hf haz) (hf hbz)
      exact G.triangle hqa hqz (hf haz) (hf hat) (hf (G.symmetric htz))
  intro t hpt
  by_cases hxt : rel x t
  · exact step hpx hpy hpt hxy hqx hqy hxt
  · obtain ⟨z,hpz,hxz,hyz,htz⟩ := G.bridge hpx hpy hpt hxy (fun h=>hxt h.1)
    have hqz := G.triangle hqx hqy (hf hxy) (hf hxz) (hf hyz)
    exact step hpz hpx hpt (G.symmetric hxz) hqz hqx (G.symmetric htz)

theorem exists_star_map (f : L → L) (hf : ∀ {x y}, rel x y → rel (f x) (f y)) :
    ∃ g : P → P, ∀ p t, G.incident p t → G.incident (g p) (f t) := by
  classical
  have h : ∀ p, ∃ q, ∀ t, G.incident p t → G.incident q (f t) := by
    intro p
    obtain ⟨x,y,hpx,hpy,hxy⟩ := G.seed p
    obtain ⟨q,hqx,hqy⟩ := G.edgePoint (hf hxy)
    exact ⟨q,fun _ hpt=>map_star_into G f hf hpx hpy hxy hqx hqy hpt⟩
  choose g hg using h
  exact ⟨g,hg⟩

theorem exists_point_equiv (f : L ≃ L)
    (hf : ∀ x y, rel (f x) (f y) ↔ rel x y) :
    ∃ g : P ≃ P, ∀ p t, G.incident (g p) (f t) ↔ G.incident p t := by
  classical
  obtain ⟨g,hg⟩ := exists_star_map G f (fun {x y} h=>(hf x y).mpr h)
  have hfi : ∀ {x y}, rel x y → rel (f.symm x) (f.symm y) := by
    intro x y h
    apply (hf (f.symm x) (f.symm y)).mp
    simpa only [f.apply_symm_apply] using h
  obtain ⟨h,hh⟩ := exists_star_map G f.symm hfi
  have hleft : ∀ p, h (g p)=p := by
    intro p
    obtain ⟨x,y,hpx,hpy,hxy⟩ := G.seed p
    have hx := hh (g p) (f x) (hg p x hpx)
    have hy := hh (g p) (f y) (hg p y hpy)
    simp only [f.symm_apply_apply] at hx hy
    exact G.uniquePoint hxy hx hy hpx hpy
  have hright : ∀ q, g (h q)=q := by
    intro q
    obtain ⟨x,y,hqx,hqy,hxy⟩ := G.seed q
    have hx := hg (h q) (f.symm x) (hh q x hqx)
    have hy := hg (h q) (f.symm y) (hh q y hqy)
    simp only [f.apply_symm_apply] at hx hy
    exact G.uniquePoint hxy hx hy hqx hqy
  refine ⟨⟨g,h,hleft,hright⟩,?_⟩
  intro p t
  constructor
  · intro hp
    have ht := hh (g p) (f t) hp
    simpa only [f.symm_apply_apply,hleft] using ht
  · exact hg p t

theorem point_equiv_unique {f : L ≃ L} {g h : P ≃ P}
    (hg : ∀ p t, G.incident (g p) (f t) ↔ G.incident p t)
    (hh : ∀ p t, G.incident (h p) (f t) ↔ G.incident p t)
    (hf : ∀ x y, rel (f x) (f y) ↔ rel x y) : g=h := by
  apply Equiv.ext
  intro p
  obtain ⟨x,y,hpx,hpy,hxy⟩ := G.seed p
  exact G.uniquePoint ((hf x y).mpr hxy) ((hg p x).mpr hpx) ((hg p y).mpr hpy)
    ((hh p x).mpr hpx) ((hh p y).mpr hpy)

end SymmetricSubgroupAsymptotics.CFSGIncidenceStarReconstruction
