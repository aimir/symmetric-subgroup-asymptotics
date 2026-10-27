import SymmetricSubgroupAsymptotics.CyclicAndActionQuotientGeneratorBudget
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Field.ZMod

/-! Actual fixed-point action of a cyclic-subgroup normalizer. If its
original faithful permutation generator is one cycle, conjugation and
fixed-point evaluation detect every element modulo that same subgroup.
A quotient killing the subgroup therefore costs cyclic-Aut rank1 plus
the rank of the actual fixed-point action image. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SingleCycleNormalizerQuotientGenerators
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X]

abbrev Normalizer (P : Subgroup G) := Subgroup.normalizer (P : Set G)
abbrev Fixed (P : Subgroup G) := MulAction.fixedPoints P X

omit [Finite G] [Finite X] [FaithfulSMul G X] in
private theorem preserves_fixed (P : Subgroup G) (u : Normalizer P) (x : Fixed (X := X) P) :
    u.val • x.val ∈ MulAction.fixedPoints P X := by
  intro p
  have hp : u.val⁻¹*p.val*u.val ∈ P := by
    have hh := ((u⁻¹).property p.val).mp p.property
    simpa only [InvMemClass.coe_inv,inv_inv] using hh
  let t : P := ⟨u.val⁻¹*p.val*u.val,hp⟩
  have he : p.val*u.val=u.val*t.val := by dsimp only [t]; group
  change p.val • (u.val • x.val)=u.val • x.val
  rw [←mul_smul,he,mul_smul]
  exact congrArg (fun y : X => u.val • y) (x.property t)

instance fixedAction (P : Subgroup G) : MulAction (Normalizer P) (Fixed (X := X) P) where
  smul u x := ⟨u.val • x.val,preserves_fixed P u x⟩
  one_smul x := Subtype.ext (one_smul G x.val)
  mul_smul u v x := Subtype.ext (mul_smul u.val v.val x.val)

def fixedHom (P : Subgroup G) : Normalizer P →* Equiv.Perm (Fixed (X := X) P) :=
  MulAction.toPermHom _ _

omit [Finite G] [Finite X] [FaithfulSMul G X] in
private theorem fixed_of_generator (P : Subgroup G) (y : G) (hP : P=Subgroup.zpowers y)
    (w : X) (hw : y • w=w) : w ∈ MulAction.fixedPoints P X := by
  have hp : P ≤ MulAction.stabilizer G w := by
    rw [hP]
    exact Subgroup.zpowers_le.mpr hw
  intro t
  exact hp t.property

theorem fixed_card [Fintype X] (P : Subgroup G) (y : G) (hP : P=Subgroup.zpowers y) (p : ℕ)
    (htype : (MulAction.toPermHom G X y).cycleType={p}) :
    Nat.card (Fixed (X := X) P)=Nat.card X-p := by
  have hy : y ∈ P := by rw [hP]; exact Subgroup.mem_zpowers y
  let e : Fixed (X := X) P ≃ Function.fixedPoints (MulAction.toPermHom G X y) := {
    toFun := fun w => ⟨w.val,w.property (⟨y,hy⟩ : P)⟩
    invFun := fun w => ⟨w.val,fixed_of_generator P y hP w.val w.property⟩
    left_inv := fun _ => Subtype.ext rfl
    right_inv := fun _ => Subtype.ext rfl }
  calc
    Nat.card (Fixed (X := X) P) =
        Nat.card (Function.fixedPoints (MulAction.toPermHom G X y)) := Nat.card_congr e
    _ = Fintype.card (Function.fixedPoints (MulAction.toPermHom G X y)) :=
      Nat.card_eq_fintype_card
    _ = Fintype.card X-(MulAction.toPermHom G X y).cycleType.sum :=
      Equiv.Perm.card_fixedPoints _
    _ = Nat.card X-p := by rw [htype,Multiset.sum_singleton,Nat.card_eq_fintype_card]

/-- Conjugation and evaluation on the actual fixed set detect a normalizer
member modulo the SAME cyclic subgroup. -/
theorem joint_kernel_le (P : Subgroup G) (y : G) (hP : P=Subgroup.zpowers y)
    (hcycle : (MulAction.toPermHom G X y).IsCycle) :
    P.normalizerMonoidHom.ker ⊓ (fixedHom (X := X) P).ker ≤
      P.subgroupOf (Normalizer P) := by
  letI : Fintype X := Fintype.ofFinite X
  let rho : G →* Equiv.Perm X := MulAction.toPermHom G X
  intro u hu
  have hy : y ∈ P := by rw [hP]; exact Subgroup.mem_zpowers y
  have he : u.val*y*u.val⁻¹=y := by
    have hh := DFunLike.congr_fun (MonoidHom.mem_ker.mp hu.1) (⟨y,hy⟩ : P)
    exact congrArg Subtype.val hh
  have hc : Commute (rho u.val) (rho y) := by
    change rho u.val*rho y=rho y*rho u.val
    rw [←map_mul,←map_mul]
    apply congrArg rho
    calc
      u.val*y = (u.val*y*u.val⁻¹)*u.val := by group
      _ = y*u.val := by rw [he]
  obtain ⟨hs,hsub⟩ := hcycle.commute_iff.mp hc
  have hout (w : X) (hw : w ∉ (rho y).support) : rho u.val w=w := by
    have hyw : y • w=w := Equiv.Perm.notMem_support.mp hw
    let z : Fixed (X := X) P := ⟨w,fixed_of_generator P y hP w hyw⟩
    have hz := Equiv.Perm.congr_fun (MonoidHom.mem_ker.mp hu.2) z
    exact congrArg Subtype.val hz
  have hfull : rho u.val=Equiv.Perm.ofSubtype ((rho u.val).subtypePerm hs) := by
    ext w
    by_cases hw : w ∈ (rho y).support
    · exact (Equiv.Perm.ofSubtype_subtypePerm_of_mem hs hw).symm
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hw]
      exact hout w hw
  obtain ⟨i,hi⟩ := Subgroup.mem_zpowers_iff.mp hsub
  have hi' : u.val=y^i := MulAction.toPerm_injective (by
    change rho u.val=rho (y^i)
    rw [map_zpow]
    exact hfull.trans hi.symm)
  change u.val ∈ P
  rw [hi']
  exact P.zpow_mem hy i

/-- Generic fixed-action budget: no whole outer bound or particular
fixed-degree estimate is built into this normalizer theorem. -/
theorem quotient_genRank_le_one_add {Q : Type} [Group Q]
    (P : Subgroup G) (y : G) (hP : P=Subgroup.zpowers y)
    [IsCyclic (MulAut P)] (hcycle : (MulAction.toPermHom G X y).IsCycle)
    (beta : Normalizer P →* Q) (hbeta : Function.Surjective beta)
    (hkill : P.subgroupOf (Normalizer P) ≤ beta.ker) (b : ℕ)
    (hfixed : MarkedC4.genRank (fixedHom (X := X) P).range ≤ b) :
    MarkedC4.genRank Q ≤ 1+b :=
  CyclicAndActionQuotientGeneratorBudget.genRank_le_one_add beta hbeta
    P.normalizerMonoidHom (fixedHom (X := X) P)
    ((joint_kernel_le P y hP hcycle).trans hkill) b hfixed

omit [Finite G] in
theorem cyclic_aut_of_prime_card (P : Subgroup G) (p : ℕ) [Fact p.Prime]
    (hcard : Nat.card P=p) : IsCyclic (MulAut P) := by
  letI : IsCyclic P := isCyclic_of_prime_card hcard
  let a := IsCyclic.mulAutMulEquiv P
  have hprime : (Nat.card P).Prime := by rw [hcard]; exact Fact.out
  letI : Fact (Nat.card P).Prime := ⟨hprime⟩
  letI : IsCyclic (ZMod (Nat.card P))ˣ := inferInstance
  exact isCyclic_of_injective a.toMonoidHom a.injective

end SymmetricSubgroupAsymptotics.SingleCycleNormalizerQuotientGenerators
