import SymmetricSubgroupAsymptotics.MinimalNormalSimpleQuotients
import SymmetricSubgroupAsymptotics.PerfectSubdirect

/-! Actual subdirect sources of a nonabelian minimal normal group are
perfect. The simple quotient coordinates are constructed from minimal
normality; they are not caller-supplied classification data. Coordinates
with ambient-normal image may vanish, and are removed only after proving
that their actual maps are trivial. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {A G ι : Type} [Group A] [Finite A] [Group G] [Fintype ι]
variable (N : Subgroup A) [N.Normal]
variable (hmin : ∀ K : Subgroup A, K.Normal → K≤N → K=⊥ ∨ K=N)
variable (hnc : ¬IsMulCommutative N)
include hmin hnc

/-- Proper subdirect relations between nonabelian minimal-normal factors
are retained. Perfectness is obtained only after constructing faithful
simple quotient coordinates. -/
theorem perfect_of_subdirect_minimal_normal (f : ι→G→*N)
    (hs : ∀i,Function.Surjective (f i))
    (hi : Function.Injective (fun x i=>f i x)) : Group.IsPerfect G := by
  classical
  letI := Fintype.ofFinite A
  obtain ⟨M,hM,hS,hP,honto,hsep⟩ :=
    nonabelian_minimal_normal_simple_coordinates N hmin hnc
  letI := hM
  letI := hS
  letI := hP
  let g (j : ι×A) : G→*(N⧸M) :=
    ((QuotientGroup.mk' M).comp (MulAut.conjNormal j.2).toMonoidHom).comp (f j.1)
  apply perfect_of_subdirect (fun _ : ι×A => N⧸M) G g
  · intro j
    exact (honto j.2).comp (hs j.1)
  · intro x y he
    apply hi
    funext i
    apply hsep
    funext a
    exact congrFun he (i,a)

/-- Every literal coordinate image is either zero or the complete local
minimal normal group. Joint injectivity still permits arbitrary proper
subdirect correlations. -/
theorem perfect_of_normal_coordinate_ranges (f : ι→G→*N)
    (hn : ∀i,((f i).range.map N.subtype).Normal)
    (hi : Function.Injective (fun x i=>f i x)) : Group.IsPerfect G := by
  classical
  have hd (i:ι) : (f i).range=⊥ ∨ Function.Surjective (f i) := by
    rcases hmin _ (hn i) (Subgroup.map_subtype_le _) with h|h
    · left
      apply Subgroup.map_injective N.subtype_injective
      simpa only [Subgroup.map_bot] using h
    · right
      apply MonoidHom.range_eq_top.mp
      apply Subgroup.map_injective N.subtype_injective
      simpa only [←MonoidHom.range_eq_map,Subgroup.range_subtype] using h
  let J := {i:ι // Function.Surjective (f i)}
  letI : Fintype J := Fintype.ofFinite J
  apply perfect_of_subdirect_minimal_normal N hmin hnc (fun j:J=>f j.1)
    (fun j=>j.2)
  intro x y he
  apply hi
  funext i
  rcases hd i with h|h
  · have hx : f i x=1 := by simpa only [h,Subgroup.mem_bot] using (show f i x∈(f i).range from ⟨x,rfl⟩)
    have hy : f i y=1 := by simpa only [h,Subgroup.mem_bot] using (show f i y∈(f i).range from ⟨y,rfl⟩)
    exact hx.trans hy.symm
  · exact congrFun he ⟨i,h⟩

end SymmetricSubgroupAsymptotics
