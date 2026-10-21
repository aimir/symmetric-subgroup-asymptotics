import SymmetricSubgroupAsymptotics.BinaryBySymmetricThree
import Mathlib.GroupTheory.Nilpotent

/-! A finite soluble group strictly larger than a central normal subgroup
has a normal nilpotent layer strictly above it. This is a minimal-normal
pullback with central kernel, not an assumed Fitting theorem. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

theorem exists_normal_nilpotent_strictly_above_central
    {G : Type} [Group G] [Finite G] [IsSolvable G]
    (Z : Subgroup G) [Z.Normal] (hZ : Z≤Subgroup.center G) (hproper : Z≠⊤) :
    ∃ B : Subgroup G,Z<B ∧ B.Normal ∧ Group.IsNilpotent B := by
  let Q := G ⧸ Z
  letI : Nontrivial Q := (QuotientGroup.nontrivial_iff).mpr hproper
  have htop : (⊤ : Subgroup Q)≠⊥ := by
    intro h
    have hc := congrArg (fun H : Subgroup Q => Nat.card H) h
    simp only [Subgroup.card_top,Subgroup.card_bot] at hc
    exact (Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial Q)).ne' hc
  let good : Subgroup Q → Prop := fun A => A.Normal ∧ A≠⊥
  obtain ⟨A,_,hmin⟩ := Finite.exists_le_minimal (p := good) (a := (⊤ : Subgroup Q))
    (show good ⊤ from ⟨inferInstance,htop⟩)
  have hA : IsMinimalNormalSubgroup A := by
    refine ⟨hmin.1.1,hmin.1.2,?_⟩
    intro K hK hKne hKA
    exact hmin.eq_of_le ⟨hK,hKne⟩ hKA
  letI : A.Normal := hA.1
  have hcomm := minimalNormal_isMulCommutative_of_isSolvable A hA
  letI : CommGroup A := { (inferInstance : Group A) with mul_comm := hcomm.is_comm.comm }
  let pi : G →* Q := QuotientGroup.mk' Z
  let B : Subgroup G := A.comap pi
  let f : B →* A := {
    toFun := fun b => ⟨pi b.val,b.property⟩
    map_one' := Subtype.ext pi.map_one
    map_mul' a b := Subtype.ext (pi.map_mul a.val b.val) }
  have hker : f.ker≤Subgroup.center B := by
    intro b hb
    have hz : b.val∈Z := by
      apply (QuotientGroup.eq_one_iff b.val).mp
      have hh : f b=1 := hb
      exact congrArg (fun a : A => a.val) hh
    apply Subgroup.mem_center_iff.mpr
    intro c
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hZ hz)) c.val
  letI : Group.IsNilpotent B := Subgroup.isNilpotent_of_ker_le_center f hker
  have hZB : Z≤B := by
    intro z hz
    change pi z∈A
    have he : pi z=1 := (QuotientGroup.eq_one_iff z).mpr hz
    rw [he]
    exact A.one_mem
  have hne : B≠Z := by
    intro he
    have hmap : B.map pi=A := Subgroup.map_comap_eq_self (by
      rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective Z)]
      exact le_top)
    have hzmap : Z.map pi=⊥ := (Subgroup.map_eq_bot_iff Z).mpr (by
      rw [QuotientGroup.ker_mk'] )
    rw [he,hzmap] at hmap
    exact hA.2.1 hmap.symm
  exact ⟨B,lt_of_le_of_ne hZB hne.symm,inferInstance,inferInstance⟩

end SymmetricSubgroupAsymptotics
