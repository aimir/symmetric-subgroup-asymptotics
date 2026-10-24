import SymmetricSubgroupAsymptotics.SemisimpleSubdirectChart
import SymmetricSubgroupAsymptotics.CFSGNormalSubgroupSimpleProduct

/-! Normal subdirect rigidity, retaining the original coordinate maps.
A normal subgroup of a semisimple source cannot project onto every
original centerless coordinate while omitting an internal simple factor.
Scott's chart is used only for this structural argument; the source is
never replaced by the full original coordinate product. No ordinary
two-generation or nonabelian minimal-normal '+1' bound is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SemisimpleNormalSubdirectRigidity

/-- In a semisimple group a normal subgroup with trivial centralizer is
the whole group. The chart permits arbitrary original diagonal relations. -/
theorem normal_eq_top_of_trivial_centralizer
    {G : Type} [Group G] (C : SemisimpleGroupChart G)
    (M : Subgroup G) [M.Normal]
    (hc : ∀ x : G, (∀ m : M, x * m.val = m.val * x) → x = 1) : M = ⊤ := by
  classical
  let P : Subgroup (∀ i, C.factor i) := M.map C.equiv.toMonoidHom
  letI : P.Normal := Subgroup.Normal.map inferInstance _ C.equiv.surjective
  letI (i : C.ι) : IsSimpleGroup (C.factor i) := C.simple i
  have hnc (i : C.ι) : ¬ IsMulCommutative (C.factor i) := by
    intro hcomm
    obtain ⟨a, ha⟩ := exists_ne (1 : C.factor i)
    exact ha (C.centerless i a (fun b => (isMulCommutative_iff.mp hcomm) a b))
  have hcP : ∀ x : (∀ i, C.factor i),
      (∀ m : P, x * m.val = m.val * x) → x = 1 := by
    intro x hx
    have he : C.equiv.symm x = 1 := by
      apply hc
      intro m
      apply C.equiv.injective
      simpa only [map_mul, C.equiv.apply_symm_apply] using
        hx (⟨C.equiv m.val, ⟨m.val, m.property, rfl⟩⟩ : P)
    have hh := congrArg C.equiv he
    simpa only [C.equiv.apply_symm_apply, map_one] using hh
  have hrange (i : C.ι) : P.map (Pi.evalMonoidHom C.factor i) = ⊤ := by
    have honto : Function.Surjective (Pi.evalMonoidHom C.factor i) := by
      intro a
      exact ⟨Pi.mulSingle i a, Pi.mulSingle_eq_same i a⟩
    have hn : (P.map (Pi.evalMonoidHom C.factor i)).Normal :=
      Subgroup.Normal.map inferInstance _ honto
    rcases hn.eq_bot_or_eq_top with hz | ht
    · obtain ⟨a, ha⟩ := exists_ne (1 : C.factor i)
      let x : ∀ j, C.factor j := Pi.mulSingle i a
      have hx : x = 1 := by
        apply hcP
        intro m
        funext j
        by_cases hj : j = i
        · subst j
          have hm : m.val i = 1 := by
            have hmem : m.val i ∈ P.map (Pi.evalMonoidHom C.factor i) :=
              ⟨m.val, m.property, rfl⟩
            rw [hz] at hmem
            exact Subgroup.mem_bot.mp hmem
          simp only [x, Pi.mul_apply, Pi.mulSingle_eq_same, hm, mul_one, one_mul]
        · simp only [x, Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, one_mul, mul_one]
      have hh : a = 1 := by
        simpa only [x, Pi.mulSingle_eq_same, Pi.one_apply] using congrFun hx i
      exact (ha hh).elim
    · exact ht
  have hP : P = ⊤ := by
    rw [CFSGNormalSubgroupSimpleProduct.normal_eq_coordinate_product C.factor hnc P]
    apply top_unique
    intro x _
    change ∀ i ∈ Set.univ, x i ∈ P.map (Pi.evalMonoidHom C.factor i)
    intro i _
    rw [hrange i]
    trivial
  apply top_unique
  intro g _
  have hg : C.equiv g ∈ P := by rw [hP]; trivial
  obtain ⟨m, hm, he⟩ := hg
  exact C.equiv.injective he ▸ hm

/-- Jointly faithful original coordinates force a trivial centralizer
as soon as the ACTUAL subgroup maps onto each centerless target. -/
theorem centralizer_trivial_of_surjective_restrictions
    {G I : Type} [Group G] (S : I → Type) [∀ i, Group (S i)]
    (hcenterless : ∀ i, IsCenterless (S i))
    (f : ∀ i, G →* S i) (hi : Function.Injective (fun g i => f i g))
    (M : Subgroup G)
    (hs : ∀ i, Function.Surjective ((f i).comp M.subtype)) :
    ∀ x : G, (∀ m : M, x * m.val = m.val * x) → x = 1 := by
  intro x hx
  apply hi
  funext i
  change f i x = f i 1
  rw [map_one]
  apply hcenterless i
  intro y
  obtain ⟨m, hm⟩ := hs i y
  have hh := congrArg (f i) (hx m)
  simp only [map_mul] at hh
  change f i x * ((f i).comp M.subtype) m =
    ((f i).comp M.subtype) m * f i x at hh
  simpa only [hm] using hh

/-- The original normal-subdirect rigidity statement. Surjectivity of
the larger source is derived from the smaller actual subgroup. -/
theorem normal_subdirect_eq_top
    {G I : Type} [Group G] [Fintype I]
    (S : I → Type) [∀ i, Group (S i)] [∀ i, Finite (S i)]
    [∀ i, IsSimpleGroup (S i)] (hcenterless : ∀ i, IsCenterless (S i))
    (f : ∀ i, G →* S i) (hi : Function.Injective (fun g i => f i g))
    (M : Subgroup G) [M.Normal]
    (hs : ∀ i, Function.Surjective ((f i).comp M.subtype)) : M = ⊤ := by
  have hfull (i : I) : Function.Surjective (f i) := by
    intro x
    obtain ⟨m, hm⟩ := hs i x
    exact ⟨m.val, hm⟩
  obtain ⟨C⟩ := semisimpleGroupChart_of_subdirect S hcenterless G f hfull hi
  exact normal_eq_top_of_trivial_centralizer C M
    (centralizer_trivial_of_surjective_restrictions S hcenterless f hi M hs)

end SymmetricSubgroupAsymptotics.SemisimpleNormalSubdirectRigidity
