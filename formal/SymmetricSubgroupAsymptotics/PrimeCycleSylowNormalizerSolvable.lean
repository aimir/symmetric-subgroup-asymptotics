import SymmetricSubgroupAsymptotics.CyclicNormalizerSolvableOfCentralizer
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.GroupTheory.Sylow

/-! A single prime cycle with at most one fixed point has cyclic ambient
centralizer. Faithful transport retains the actual source centralizer,
and a prime-cardinality subgroup therefore has soluble normalizer.
No named-group, census, or Frattini-rank premise is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimeCycleSylowNormalizerSolvable

theorem ambient_centralizer_card {p n : ℕ} (g : Equiv.Perm (Fin n))
    (hn : n = p ∨ n = p + 1) (htype : g.cycleType = {p}) :
    Nat.card (Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin n)))) = p := by
  rw [Equiv.Perm.nat_card_centralizer,htype]
  rcases hn with rfl | rfl
  · simp
  · have hs : p + 1 - p = 1 := by omega
    simp [hs]

variable {G : Type*} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]
    [MulAction G (Fin n)] [FaithfulSMul G (Fin n)]

theorem centralizer_isCyclic (P : Subgroup G) (y : G) (hy : y ∈ P)
    (hn : n = p ∨ n = p + 1)
    (htype : (MulAction.toPermHom G (Fin n) y).cycleType = {p}) :
    IsCyclic (Subgroup.centralizer (P : Set G)) := by
  let rho := MulAction.toPermHom G (Fin n)
  let C := Subgroup.centralizer ({rho y} : Set (Equiv.Perm (Fin n)))
  letI : IsCyclic C := isCyclic_of_prime_card (ambient_centralizer_card (rho y) hn htype)
  let f : Subgroup.centralizer (P : Set G) →* C := {
    toFun := fun x => ⟨rho x.val,by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have hh := Subgroup.mem_centralizer_iff.mp x.property y hy
      simpa only [←map_mul] using (congrArg rho hh).symm⟩
    map_one' := Subtype.ext rho.map_one
    map_mul' x z := Subtype.ext (rho.map_mul x.val z.val) }
  apply isCyclic_of_injective f
  intro x z h
  apply Subtype.ext
  exact MulAction.toPerm_injective (congrArg Subtype.val h)

theorem centralizer_isSolvable (P : Subgroup G) (y : G) (hy : y ∈ P)
    (hn : n = p ∨ n = p + 1)
    (htype : (MulAction.toPermHom G (Fin n) y).cycleType = {p}) :
    IsSolvable (Subgroup.centralizer (P : Set G)) := by
  letI := centralizer_isCyclic P y hy hn htype
  exact isSolvable_of_comm (fun a b => mul_comm' a b)

theorem subgroup_normalizer_isSolvable (P : Subgroup G) (hP : Nat.card P = p)
    (y : G) (hy : y ∈ P) (hn : n = p ∨ n = p + 1)
    (htype : (MulAction.toPermHom G (Fin n) y).cycleType = {p}) :
    IsSolvable (Subgroup.normalizer (P : Set G)) := by
  letI : IsCyclic P := isCyclic_of_prime_card hP
  exact CyclicNormalizerSolvableOfCentralizer.isSolvable P
    (centralizer_isSolvable P y hy hn htype)

theorem sylow_normalizer_isSolvable (P : Sylow p G) (hP : Nat.card P = p)
    (y : G) (hy : y ∈ P) (hn : n = p ∨ n = p + 1)
    (htype : (MulAction.toPermHom G (Fin n) y).cycleType = {p}) :
    IsSolvable (Subgroup.normalizer (P : Set G)) :=
  subgroup_normalizer_isSolvable (P : Subgroup G) hP y hy hn htype

end SymmetricSubgroupAsymptotics.PrimeCycleSylowNormalizerSolvable
