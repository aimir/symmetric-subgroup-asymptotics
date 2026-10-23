import SymmetricSubgroupAsymptotics.SubnormalCoordinateClassBound
import SymmetricSubgroupAsymptotics.ConjugacyClassRealCoordinateBound

/-! Arbitrary finite index sets and real budgets for the genuine
subnormal-coordinate filtration. Only the actual image's subnormality
and budgets for subnormal component subgroups are inputs; correlations
among coordinates are retained throughout. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.SubnormalRealCoordinateClassBound
open SubnormalCoordinateClassBound

theorem class_card_le_finite_subnormal_coordinate_bounds
    {ι : Type*} [Fintype ι] (V : ι→Type*) [∀i,Group (V i)] [∀i,Finite (V i)]
    (c : ι→ℕ) (H : Type*) [Group H] [Finite H] (f : ∀i,H→*V i)
    (himage : ∀i,(f i).range.IsSubnormal)
    (hc : ∀i (L : Subgroup (V i)),L.IsSubnormal→Nat.card (ConjClasses L)≤c i)
    (hinj : Function.Injective (fun x=>fun i=>f i x)) :
    Nat.card (ConjClasses H)≤∏i,c i := by
  let e := (Fintype.equivFin ι).symm
  have hi : Function.Injective (fun x=>fun j=>f (e j) x) := by
    intro x y he
    apply hinj
    funext i
    obtain ⟨j,rfl⟩ := e.surjective i
    exact congrFun he j
  have hh := class_card_le_subnormal_coordinate_bounds (Fintype.card ι)
    (fun j=>V (e j)) (fun j=>c (e j)) (fun j=>f (e j))
    (fun j=>himage (e j)) (fun j=>hc (e j)) hi
  simpa only [e.prod_comp] using hh

theorem real_class_card_le_finite_subnormal_coordinate_bounds
    {ι : Type*} [Fintype ι] (V : ι→Type*) [∀i,Group (V i)] [∀i,Finite (V i)]
    (c : ι→ℝ) (hc0 : ∀i,0≤c i)
    (H : Type*) [Group H] [Finite H] (f : ∀i,H→*V i)
    (himage : ∀i,(f i).range.IsSubnormal)
    (hc : ∀i (L : Subgroup (V i)),L.IsSubnormal→(Nat.card (ConjClasses L):ℝ)≤c i)
    (hinj : Function.Injective (fun x=>fun i=>f i x)) :
    (Nat.card (ConjClasses H):ℝ)≤∏i,c i := by
  have hn := class_card_le_finite_subnormal_coordinate_bounds V (fun i=>Nat.floor (c i))
    H f himage (fun i L hL=>(Nat.le_floor_iff (hc0 i)).mpr (hc i L hL)) hinj
  have hcast : (Nat.card (ConjClasses H):ℝ)≤∏i,(Nat.floor (c i):ℝ) := by exact_mod_cast hn
  apply hcast.trans
  exact Finset.prod_le_prod (fun _ _=>Nat.cast_nonneg _) (fun i _=>Nat.floor_le (hc0 i))

end SymmetricSubgroupAsymptotics.SubnormalRealCoordinateClassBound
