import SymmetricSubgroupAsymptotics.TransitiveProductAxisThreeDivisor
import SymmetricSubgroupAsymptotics.MinimalTransitiveNonabelianNormalOrbitNotPrimePower

/-! At least one actual factor-point-stabilizer index contains3, in the
SAME original minimal-transitive action and SAME normal-subgroup chart. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MinimalTransitiveActualFactorThreeDivisor
variable {G X J T : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
  [FaithfulSMul G X] [MulAction.IsPretransitive G X]
  [Group T] [Finite T] [Fintype J] [DecidableEq J]

def axisInclusion (L : Subgroup G) (e : L ≃* (J → T)) (i : J) : T →* G :=
  L.subtype.comp (e.symm.toMonoidHom.comp (MonoidHom.mulSingle (fun _ : J => T) i))

theorem exists_actual_factor_three_divisor
    (hmin : ∀ N : Subgroup G, MulAction.IsPretransitive N X → N=⊤)
    (L : Subgroup G) (hL : IsMinimalNormalSubgroup L)
    (hnc : ¬IsMulCommutative L) (e : L ≃* (J → T))
    (m : ℕ) (hdegree : Nat.card X=3*2^m) (x : X) :
    ∃ i : J,
      letI : MulAction T X := MulAction.compHom X (axisInclusion L e i)
      3 ∣ (MulAction.stabilizer T x).index := by
  letI : L.Normal := hL.1
  let Y := MulAction.orbit L x
  let x' : Y := ⟨x,MulAction.mem_orbit_self x⟩
  letI : MulAction.IsPretransitive L Y := ⟨by
    intro y z
    obtain ⟨a,ha⟩ := MulAction.mem_orbit_iff.mp y.property
    obtain ⟨b,hb⟩ := MulAction.mem_orbit_iff.mp z.property
    refine ⟨b*a⁻¹,Subtype.ext ?_⟩
    change (b*a⁻¹) • y.val=z.val
    rw [←ha,mul_smul,inv_smul_smul,hb]⟩
  letI : MulAction (J → T) Y := MulAction.compHom Y e.symm.toMonoidHom
  letI : MulAction.IsPretransitive (J → T) Y := ⟨by
    intro y z
    obtain ⟨l,hl⟩ := MulAction.exists_smul_eq L y z
    refine ⟨e l,?_⟩
    change e.symm (e l) • y=z
    rw [e.symm_apply_apply]
    exact hl⟩
  have hd : Nat.card Y ∣ 3*2^m := by
    have hh := (MulAction.IsBlock.orbit_of_normal (N:=L) x).ncard_dvd_card
      ⟨x,MulAction.mem_orbit_self x⟩
    simpa only [hdegree] using hh
  have hn (r : ℕ) : Nat.card Y ≠ 2^r :=
    MinimalTransitiveNonabelianNormalOrbitNotPrimePower.orbit_card_ne_two_power
      hmin L hL hnc r x
  obtain ⟨i,hi⟩ := TransitiveProductAxisThreeDivisor.exists_axis_three_divisor (J:=J) (T:=T) (X:=Y) m x' hd hn
  refine ⟨i,?_⟩
  letI : MulAction T X := MulAction.compHom X (axisInclusion L e i)
  letI : MulAction T Y := ProductAxisPrimePowerOrbit.axisAction i
  have heq : MulAction.stabilizer T x'=MulAction.stabilizer T x := by
    ext t
    constructor
    · intro ht
      exact congrArg Subtype.val ht
    · intro ht
      exact Subtype.ext ht
  change 3 ∣ (MulAction.stabilizer T x').index at hi
  rw [heq] at hi
  exact hi

end SymmetricSubgroupAsymptotics.MinimalTransitiveActualFactorThreeDivisor
