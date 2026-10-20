import SymmetricSubgroupAsymptotics.MinimalNormalCompositionCharts
import SymmetricSubgroupAsymptotics.ZmudFaithfulCharacterInput

/-! The homogeneous simple-power chart of one actual nonabelian minimal
normal subgroup. Scott's already proved coordinate chart retains the common
simple quotient as the origin of every factor. No primitive classification
or O'Nan--Scott input is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleONanScottHelpers

structure HomogeneousNonabelianChart (E : Type) [Group E] where
  Simple : Type
  [group : Group Simple]
  [finite : Finite Simple]
  [simple : IsSimpleGroup Simple]
  noncommutative : ¬ IsMulCommutative Simple
  factorCount : ℕ
  factorCount_pos : 0 < factorCount
  equiv : E ≃* (Fin factorCount → Simple)

attribute [instance] HomogeneousNonabelianChart.group
  HomogeneousNonabelianChart.finite HomogeneousNonabelianChart.simple

/-- A homogeneous chart with an actual common simple quotient, constructed
from the ambient conjugates of one maximal normal kernel. -/
theorem minimal_normal_homogeneous_nonempty
    {G : Type} [Group G] [Finite G]
    (E : Subgroup G) [E.Normal]
    (hmin : ∀ K : Subgroup G, K.Normal → K ≤ E → K=⊥ ∨ K=E)
    (hnc : ¬ IsMulCommutative E) :
    Nonempty (HomogeneousNonabelianChart E) := by
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨M,hM,hS,hP,honto,hsep⟩ :=
    nonabelian_minimal_normal_simple_coordinates E hmin hnc
  letI : M.Normal := hM
  letI : IsSimpleGroup (E ⧸ M) := hS
  letI : Group.IsPerfect (E ⧸ M) := hP
  let T := E ⧸ M
  have hTnc : ¬ IsMulCommutative T := by
    intro hc
    have hb : commutator T = ⊥ := (commutator_eq_bot_iff T).mpr hc
    have he : (⊥ : Subgroup T)=⊤ := hb.symm.trans Group.IsPerfect.commutator_eq_top
    exact bot_ne_top he
  obtain ⟨C⟩ := semisimpleGroupChartOrigins_of_subdirect (fun _ : G => T)
    (fun _ => isCenterless_of_simple_perfect T) E
    (fun a => (QuotientGroup.mk' M).comp
      (MulAut.conjNormal (H := E) a).toMonoidHom) honto hsep
  have hk : 0 < Fintype.card C.ι := by
    by_contra h
    have hz : Fintype.card C.ι=0 := by omega
    letI : IsEmpty C.ι := Fintype.card_eq_zero_iff.mp hz
    apply hnc
    exact isMulCommutative_iff.mpr (fun a b =>
      C.equiv.injective (Subsingleton.elim _ _))
  let e : E ≃* (Fin (Fintype.card C.ι) → T) :=
    C.equiv.trans ((MulEquiv.piCongrRight C.factor_equiv).trans
      (MulEquiv.arrowCongr (Fintype.equivFin C.ι) (MulEquiv.refl T)))
  exact ⟨{
    Simple := T
    noncommutative := hTnc
    factorCount := Fintype.card C.ι
    factorCount_pos := hk
    equiv := e }⟩

/-- The same theorem on a literal minimal normal subgroup of the original
ambient group. The minimality premise is the standard lattice predicate. -/
theorem chart_of_minimalNormal_nonempty
    {G : Type} [Group G] [Finite G]
    (E : Subgroup G) (hE : IsMinimalNormalSubgroup E)
    (hnc : ¬ IsMulCommutative E) :
    Nonempty (HomogeneousNonabelianChart E) := by
  letI : E.Normal := hE.1
  apply minimal_normal_homogeneous_nonempty E ?_ hnc
  intro K hK hle
  by_cases hz : K=⊥
  · exact Or.inl hz
  · exact Or.inr (hE.2.2 K hK hz hle)

end SymmetricSubgroupAsymptotics.PrimitiveSocleONanScottHelpers
