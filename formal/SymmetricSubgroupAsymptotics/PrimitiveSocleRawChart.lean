import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScott

/-! Internal choices and centerlessness for the bare O'Nan--Scott chart.
Neither a least index nor a semisimple numerical profile is a raw field. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

theorem exists_leastProperIndex (T : Type) [Group T] [IsSimpleGroup T] :
    ∃ ell : ℕ, LeastProperIndex T ell := by
  let good : ℕ → Prop := fun n =>
    ∃ H : Subgroup T, H ≠ ⊤ ∧ H.index = n
  have hex : ∃ n, good n :=
    ⟨(⊥ : Subgroup T).index, ⊥, bot_ne_top, rfl⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  intro H hH
  exact Nat.find_min' hex ⟨H,hH,rfl⟩

theorem centerless_of_nonabelian_simple (T : Type) [Group T]
    [IsSimpleGroup T] (hnc : ¬ IsMulCommutative T) : IsCenterless T := by
  intro x hx
  have hxcenter : x ∈ Subgroup.center T :=
    Subgroup.mem_center_iff.mpr (fun y => (hx y).symm)
  rcases Subgroup.Normal.eq_bot_or_eq_top
      (H := Subgroup.center T) inferInstance with hbot | htop
  · rw [hbot, Subgroup.mem_bot] at hxcenter
    exact hxcenter
  · exact False.elim (hnc (isMulCommutative_iff.mpr (fun a b => by
      have ha : a ∈ Subgroup.center T := by
        rw [htop]
        exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm)))

/-- The semisimple chart is on the original full socle, with exactly the
factor count of the structural classification. -/
def NonaffineData.chart {G X : Type} [Group G] [Finite G]
    [Finite X] [MulAction G X] (D : NonaffineData G X) :
    SemisimpleNormalChart (finiteGroupSocle G) where
  ι := Fin D.factorCount
  factor := fun _ => D.Simple
  simple := fun _ => inferInstance
  centerless := fun _ => centerless_of_nonabelian_simple D.Simple D.noncommutative
  equiv := D.socleEquiv

@[simp] theorem NonaffineData.chart_card {G X : Type} [Group G] [Finite G]
    [Finite X] [MulAction G X] (D : NonaffineData G X) :
    Fintype.card D.chart.ι = D.factorCount := Fintype.card_fin _

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
