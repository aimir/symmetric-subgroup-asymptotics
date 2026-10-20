import SymmetricSubgroupAsymptotics.PrimitiveSocleHomogeneousMinimalNormal
import SymmetricSubgroupAsymptotics.PrimitiveCatalogueClassificationAssembly
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.Algebra.Module.ZMod

/-! The affine alternative follows from an actual abelian minimal normal
subgroup. The primitive action forces transitivity, and commutativity forces
regularity on the same original point set. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleONanScottHelpers

variable {G X : Type} [Group G] [MulAction G X] [FaithfulSMul G X]

/-- Every nontrivial normal subgroup of an actual faithful primitive group
is transitive on its original points. -/
theorem normal_transitive_of_ne_bot [MulAction.IsPreprimitive G X]
    (N : Subgroup G) [N.Normal] (hne : N≠⊥) :
    MulAction.IsPretransitive N X := by
  have hfixed : MulAction.fixedPoints N X ≠ Set.univ := by
    intro hall
    apply hne
    apply le_antisymm _ bot_le
    intro n hn
    apply Subgroup.mem_bot.mpr
    apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
    intro x
    have hx : x ∈ MulAction.fixedPoints N X := by rw [hall]; exact Set.mem_univ x
    exact (hx ⟨n,hn⟩).trans (one_smul G x).symm
  exact MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hfixed

/-- A transitive abelian subgroup acts freely in the original faithful
action. No normality premise is needed for this step. -/
theorem abelian_transitive_free (N : Subgroup G)
    [MulAction.IsPretransitive N X] (hcomm : IsMulCommutative N)
    (x : X) (n : N) (hn : n • x=x) : n=1 := by
  apply eq_of_smul_eq_smul (α := X)
  intro y
  obtain ⟨t,ht⟩ := MulAction.exists_smul_eq N x y
  have hnt : n*t=t*n := isMulCommutative_iff.mp hcomm n t
  calc
    n • y = n • (t • x) := by rw [ht]
    _ = t • (n • x) := by rw [←mul_smul,hnt,mul_smul]
    _ = y := by rw [hn,ht]
    _ = (1 : N) • y := (one_smul N y).symm

/-- The transitive and free witnesses retain literal subgroup elements. -/
theorem abelian_transitive_regular (N : Subgroup G)
    [MulAction.IsPretransitive N X] (hcomm : IsMulCommutative N) :
    ∀ x y : X, ∃! n : N, n • x=y := by
  intro x y
  obtain ⟨n,hn⟩ := MulAction.exists_smul_eq N x y
  refine ⟨n,hn,?_⟩
  intro t ht
  have hf : n⁻¹*t=1 := abelian_transitive_free N hcomm x (n⁻¹*t) (by
    rw [mul_smul,ht,←hn,inv_smul_smul])
  exact (inv_mul_eq_one.mp hf).symm

/-- An actual abelian minimal normal subgroup supplies the full retained
affine profile, without any published primitive classification. -/
theorem affineProfile_of_abelian_minimal_nonempty [Finite G]
    [MulAction.IsPreprimitive G X]
    (E : Subgroup G) (hE : IsMinimalNormalSubgroup E)
    (hcomm : IsMulCommutative E) :
    Nonempty (PrimitiveAffineProfile G X) := by
  letI : E.Normal := hE.1
  have hmin : ∀ K : Subgroup G, K.Normal → K≤E → K=⊥ ∨ K=E := by
    intro K hK hle
    by_cases hz : K=⊥
    · exact Or.inl hz
    · exact Or.inr (hE.2.2 K hK hz hle)
  obtain ⟨C⟩ := elementaryMinimalNormalChart_nonempty E hE.2.1 hcomm hmin
  letI : MulAction.IsPretransitive E X := normal_transitive_of_ne_bot E hE.2.1
  have hp : IsPGroup C.p E :=
    (ZModModule.isPGroup_multiplicative (n := C.p) (G := C.V)).of_equiv C.equiv.symm
  exact ⟨{
    p := C.p
    p_prime := C.p_prime
    V := E
    V_pgroup := hp
    regular := abelian_transitive_regular E hcomm }⟩

/-- The full original socle is transitive as soon as one actual minimal
normal subgroup has been selected. -/
theorem full_socle_transitive [MulAction.IsPreprimitive G X]
    (E : Subgroup G) (hE : IsMinimalNormalSubgroup E) :
    MulAction.IsPretransitive (finiteGroupSocle G) X := by
  letI : E.Normal := hE.1
  letI : MulAction.IsPretransitive E X := normal_transitive_of_ne_bot E hE.2.1
  refine ⟨?_⟩
  intro x y
  obtain ⟨e,he⟩ := MulAction.exists_smul_eq E x y
  exact ⟨⟨(e : G),Subgroup.subset_normalClosure ⟨E,hE,e.property⟩⟩,he⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleONanScottHelpers
