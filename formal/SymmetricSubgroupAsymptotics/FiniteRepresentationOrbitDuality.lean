import SymmetricSubgroupAsymptotics.TraceySolubleOrbitInducedInput
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! A finite-field representation and its contragredient have the same
number of nonzero-vector orbits. This is Burnside's lemma on the actual
original group, using equality of fixed-space ranks for each element. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics.FiniteRepresentationOrbitDuality

variable {k G V : Type} [Field k] [Group G]
    [AddCommGroup V] [Module k V]

def fixedSpace (rho : Representation k G V) (g : G) : Submodule k V :=
  LinearMap.ker (rho g - LinearMap.id)

@[simp] theorem mem_fixedSpace (rho : Representation k G V) (g : G) (v : V) :
    v ∈ fixedSpace rho g ↔ rho g v = v := by
  simp only [fixedSpace,LinearMap.mem_ker,LinearMap.sub_apply,LinearMap.id_apply,sub_eq_zero]

theorem fixedSpace_inv (rho : Representation k G V) (g : G) :
    fixedSpace rho g⁻¹ = fixedSpace rho g := by
  ext v
  simp only [mem_fixedSpace]
  constructor
  · intro h
    have he := congrArg (rho g) h
    change (rho g * rho g⁻¹) v = rho g v at he
    rw [← map_mul,mul_inv_cancel,map_one] at he
    exact he.symm
  · intro h
    have he := congrArg (rho g⁻¹) h
    change (rho g⁻¹ * rho g) v = rho g⁻¹ v at he
    rw [← map_mul,inv_mul_cancel,map_one] at he
    exact he.symm

theorem fixedSpace_dual_finrank [FiniteDimensional k V]
    (rho : Representation k G V) (g : G) :
    Module.finrank k (fixedSpace rho.dual g) = Module.finrank k (fixedSpace rho g) := by
  have hd : rho.dual g - LinearMap.id = (rho g⁻¹ - LinearMap.id).dualMap := by
    ext f v
    simp only [LinearMap.sub_apply,LinearMap.id_apply,Representation.dual_apply,
      Module.Dual.transpose_apply,LinearMap.dualMap_apply,LinearMap.comp_apply,map_sub]
  have h1 := (rho g⁻¹ - LinearMap.id).finrank_range_add_finrank_ker
  have h2 := (rho g⁻¹ - LinearMap.id).dualMap.finrank_range_add_finrank_ker
  rw [LinearMap.finrank_range_dualMap_eq_finrank_range,Subspace.dual_finrank_eq] at h2
  have he : Module.finrank k (fixedSpace rho.dual g) =
      Module.finrank k (fixedSpace rho g⁻¹) := by
    unfold fixedSpace
    rw [hd]
    omega
  exact he.trans (congrArg (fun W : Submodule k V => Module.finrank k W) (fixedSpace_inv rho g))

/-- The action on the actual nonzero vectors. -/
@[implicit_reducible] def nonzeroAction (rho : Representation k G V) : MulAction G {v : V // v ≠ 0} where
  smul g x := ⟨rho g x.1,by
    intro hz
    apply x.2
    have he := congrArg (rho g⁻¹) hz
    rw [map_zero] at he
    change (rho g⁻¹ * rho g) x.1 = 0 at he
    rw [← map_mul,inv_mul_cancel,map_one] at he
    exact he⟩
  one_smul x := by apply Subtype.ext;change rho 1 x.1=x.1;rw [map_one];rfl
  mul_smul g h x := by apply Subtype.ext;change rho (g*h) x.1=rho g (rho h x.1);rw [map_mul];rfl

private def nonzeroFixedEquiv (rho : Representation k G V) (g : G) :
    letI := nonzeroAction rho
    MulAction.fixedBy {v : V // v ≠ 0} g ≃ {v : fixedSpace rho g // v ≠ 0} := by
  letI := nonzeroAction rho
  refine {
    toFun := fun x => ⟨⟨x.1.1,(mem_fixedSpace rho g x.1.1).mpr
      (congrArg Subtype.val x.2)⟩,?_⟩
    invFun := fun x => ⟨⟨x.1.1,?_⟩,?_⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  · intro h
    exact x.1.2 (congrArg Subtype.val h)
  · intro h
    apply x.2
    exact Subtype.ext h
  · apply Subtype.ext
    exact (mem_fixedSpace rho g x.1.1).mp x.1.2

private theorem card_nonzero {A : Type} [Zero A] [Finite A] :
    Nat.card {a : A // a ≠ 0} = Nat.card A - 1 := by
  simp [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]

private def nonzeroOrbitEquiv (rho : Representation k G V) :
    letI := nonzeroAction rho
    Quotient (representationNonzeroOrbitRel rho) ≃
      MulAction.orbitRel.Quotient G {v : V // v ≠ 0} := by
  letI := nonzeroAction rho
  apply Quotient.congr (Equiv.refl _)
  intro x y
  change (∃ g : G,rho g x.1=y.1) ↔ _
  rw [MulAction.orbitRel_apply,MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g,hg⟩
    refine ⟨g⁻¹,Subtype.ext ?_⟩
    change rho g⁻¹ y.1=x.1
    rw [← hg]
    change (rho g⁻¹ * rho g) x.1=x.1
    rw [← map_mul,inv_mul_cancel,map_one];rfl
  · rintro ⟨g,hg⟩
    refine ⟨g⁻¹,?_⟩
    change rho g⁻¹ x.1=y.1
    have hg' : rho g y.1 = x.1 := congrArg Subtype.val hg
    rw [← hg']
    change (rho g⁻¹ * rho g) y.1=y.1
    rw [← map_mul,inv_mul_cancel,map_one];rfl

/-- No faithfulness or coprimality is required. -/
theorem nonzero_orbit_card_dual [Finite k] [Finite G] [FiniteDimensional k V]
    (rho : Representation k G V) :
    Nat.card (Quotient (representationNonzeroOrbitRel rho.dual)) =
      Nat.card (Quotient (representationNonzeroOrbitRel rho)) := by
  letI : Finite V := Module.finite_of_finite k
  letI : Finite (Module.Dual k V) := Module.finite_of_finite k
  letI := nonzeroAction rho
  letI := nonzeroAction rho.dual
  have hc (g : G) :
      Nat.card (MulAction.fixedBy {v : Module.Dual k V // v ≠ 0} g) =
        Nat.card (MulAction.fixedBy {v : V // v ≠ 0} g) := by
    rw [Nat.card_congr (nonzeroFixedEquiv rho.dual g),
      Nat.card_congr (nonzeroFixedEquiv rho g),card_nonzero,card_nonzero,
      Module.natCard_eq_pow_finrank (K := k) (V := fixedSpace rho.dual g),
      Module.natCard_eq_pow_finrank (K := k) (V := fixedSpace rho g),
      fixedSpace_dual_finrank]
  have h1 := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G {v : V // v ≠ 0}
  have h2 := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G {v : Module.Dual k V // v ≠ 0}
  simp only [← Nat.card_eq_fintype_card] at h1 h2
  have hs : (∑ g : G,Nat.card (MulAction.fixedBy {v : Module.Dual k V // v ≠ 0} g)) =
      ∑ g : G,Nat.card (MulAction.fixedBy {v : V // v ≠ 0} g) := Finset.sum_congr rfl (fun g _ => hc g)
  rw [h1,h2] at hs
  have hp : 0 < Nat.card G := Nat.card_pos
  have he : Nat.card (MulAction.orbitRel.Quotient G {v : Module.Dual k V // v ≠ 0}) =
      Nat.card (MulAction.orbitRel.Quotient G {v : V // v ≠ 0}) := by nlinarith
  exact (Nat.card_congr (nonzeroOrbitEquiv rho.dual)).trans
    (he.trans (Nat.card_congr (nonzeroOrbitEquiv rho)).symm)

end SymmetricSubgroupAsymptotics.FiniteRepresentationOrbitDuality
