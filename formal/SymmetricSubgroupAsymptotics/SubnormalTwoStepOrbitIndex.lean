import Mathlib.GroupTheory.GroupAction.Blocks
import Mathlib.GroupTheory.Index
import Mathlib.SetTheory.Cardinal.Finite

/-! An actual factor normal in an actual normal subgroup has point
stabilizer index dividing the ORIGINAL transitive degree. This is the
index-divisibility seam before simple-group subgroup classification. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SubnormalTwoStepOrbitIndex
variable {G X : Type*} [Group G] [MulAction G X]

def restrictedOrbitEquiv (L : Subgroup G) (K : Subgroup L) (x : X) :
    MulAction.orbit K (⟨x,MulAction.mem_orbit_self x⟩ : MulAction.orbit L x) ≃
      MulAction.orbit K x where
  toFun y := ⟨y.val.val,by
    obtain ⟨k,hk⟩ := MulAction.mem_orbit_iff.mp y.property
    exact MulAction.mem_orbit_iff.mpr ⟨k,congrArg Subtype.val hk⟩⟩
  invFun y := ⟨⟨y.val,MulAction.mem_orbit_of_mem_orbit_subgroup y.property⟩,by
    obtain ⟨k,hk⟩ := MulAction.mem_orbit_iff.mp y.property
    exact MulAction.mem_orbit_iff.mpr ⟨k,Subtype.ext hk⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem stabilizer_index_dvd_degree [Finite X] [MulAction.IsPretransitive G X]
    (L : Subgroup G) [L.Normal] (K : Subgroup L) [K.Normal] (x : X) :
    (MulAction.stabilizer K x).index ∣ Nat.card X := by
  let x' : MulAction.orbit L x := ⟨x,MulAction.mem_orbit_self x⟩
  letI : MulAction.IsPretransitive L (MulAction.orbit L x) := ⟨by
    intro y z
    obtain ⟨a,ha⟩ := MulAction.mem_orbit_iff.mp y.property
    obtain ⟨b,hb⟩ := MulAction.mem_orbit_iff.mp z.property
    refine ⟨b*a⁻¹,Subtype.ext ?_⟩
    change (b*a⁻¹) • y.val=z.val
    rw [←ha,mul_smul,inv_smul_smul,hb]⟩
  have hsmall : Nat.card (MulAction.orbit K x') ∣ Nat.card (MulAction.orbit L x) :=
    (MulAction.IsBlock.orbit_of_normal (G:=L) (N:=K) x').ncard_dvd_card
      ⟨x',MulAction.mem_orbit_self x'⟩
  have hlarge : Nat.card (MulAction.orbit L x) ∣ Nat.card X :=
    (MulAction.IsBlock.orbit_of_normal (G:=G) (N:=L) x).ncard_dvd_card
      ⟨x,MulAction.mem_orbit_self x⟩
  have hcard := Nat.card_congr (restrictedOrbitEquiv L K x)
  change Nat.card (MulAction.orbit K x')=Nat.card (MulAction.orbit K x) at hcard
  rw [hcard] at hsmall
  rw [MulAction.index_stabilizer]
  exact hsmall.trans hlarge

theorem stabilizer_index_dvd_three_two_power [Finite X] [MulAction.IsPretransitive G X]
    (L : Subgroup G) [L.Normal] (K : Subgroup L) [K.Normal]
    (x : X) (m : ℕ) (hdegree : Nat.card X=3*2^m) :
    (MulAction.stabilizer K x).index ∣ 3*2^m := by
  simpa only [hdegree] using stabilizer_index_dvd_degree L K x

end SymmetricSubgroupAsymptotics.SubnormalTwoStepOrbitIndex
