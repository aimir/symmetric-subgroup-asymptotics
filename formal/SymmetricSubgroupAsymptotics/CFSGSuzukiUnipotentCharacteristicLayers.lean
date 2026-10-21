import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentCommutator
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Intrinsic characteristic layers of the literal Suzuki unipotent group.
For the original positive parameter, its centre and derived subgroup are
exactly the original zero-first-coordinate subgroup. The first-coordinate
quotient is the additive group of the original field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical CharTwo commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
open CFSGSuzukiFieldParameters

def coordinateElement (m : ℕ) (a b : Field m) : unipotentSubgroup m :=
  ⟨unipotentElement m a b,⟨a,b,rfl⟩⟩

@[simp] theorem coordinateElement_val (m : ℕ) (a b : Field m) :
    (coordinateElement m a b : Ambient m)=unipotentElement m a b := rfl

@[simp] theorem coordinateElement_mul (m : ℕ) (a b c d : Field m) :
    coordinateElement m a b*coordinateElement m c d=
      coordinateElement m (a+c) (b+d+theta m a*c) :=
  Subtype.ext (unipotentElement_mul m a b c d)

@[simp] theorem coordinateElement_zero (m : ℕ) : coordinateElement m 0 0=1 :=
  Subtype.ext (unipotentElement_zero m)

theorem coordinateElement_commutator (m : ℕ) (a b c d : Field m) :
    ⁅coordinateElement m a b,coordinateElement m c d⁆=
      coordinateElement m 0 (theta m a*c+theta m c*a) :=
  Subtype.ext (unipotentElement_commutator m a b c d)

def firstParameter (m : ℕ) (g : unipotentSubgroup m) : Field m :=
  (g.val : CFSG.Models.SuzukiConstruction.Mat m) 1 0

@[simp] theorem firstParameter_coordinateElement (m : ℕ) (a b : Field m) :
    firstParameter m (coordinateElement m a b)=a := rfl

def firstParameterHom (m : ℕ) : unipotentSubgroup m→*Multiplicative (Field m) where
  toFun := fun g => Multiplicative.ofAdd (firstParameter m g)
  map_one' := by
    change (1 : CFSG.Models.SuzukiConstruction.Mat m) 1 0=0
    simp
  map_mul' := by
    intro g h
    obtain ⟨a,b,hg⟩ := g.property
    obtain ⟨c,d,hh⟩ := h.property
    change ((g.val*h.val : Ambient m) : CFSG.Models.SuzukiConstruction.Mat m) 1 0=
      (g.val : CFSG.Models.SuzukiConstruction.Mat m) 1 0+
      (h.val : CFSG.Models.SuzukiConstruction.Mat m) 1 0
    rw [hg,hh,unipotentElement_mul]
    rfl

@[simp] theorem firstParameterHom_coordinateElement (m : ℕ) (a b : Field m) :
    firstParameterHom m (coordinateElement m a b)=Multiplicative.ofAdd a := rfl

theorem firstParameterHom_surjective (m : ℕ) : Function.Surjective (firstParameterHom m) := by
  intro a
  exact ⟨coordinateElement m a.toAdd 0,rfl⟩

def centralParameters (m : ℕ) : Subgroup (unipotentSubgroup m) :=
  (firstParameterHom m).ker

instance suzukiCentralParameters_normal (m : ℕ) : (centralParameters m).Normal := by
  change (firstParameterHom m).ker.Normal
  infer_instance

@[simp] theorem mem_centralParameters (m : ℕ) (g : unipotentSubgroup m) :
    g∈centralParameters m↔firstParameter m g=0 := Iff.rfl

@[simp] theorem coordinateElement_mem_centralParameters (m : ℕ) (a b : Field m) :
    coordinateElement m a b∈centralParameters m↔a=0 := Iff.rfl

theorem centralParameters_le_center (m : ℕ) :
    centralParameters m≤Subgroup.center (unipotentSubgroup m) := by
  intro g hg
  obtain ⟨a,b,hgval⟩ := g.property
  have hg' : g=coordinateElement m a b := Subtype.ext hgval
  rw [hg',coordinateElement_mem_centralParameters] at hg
  subst a
  apply Subgroup.mem_center_iff.mpr
  intro h
  obtain ⟨c,d,hhval⟩ := h.property
  have hh : h=coordinateElement m c d := Subtype.ext hhval
  rw [hg',hh,coordinateElement_mul,coordinateElement_mul]
  simp only [map_zero,mul_zero,zero_mul,add_zero,zero_add,add_comm]

theorem center_le_centralParameters (m : ℕ) (hm : 1≤m) :
    Subgroup.center (unipotentSubgroup m)≤centralParameters m := by
  intro g hg
  obtain ⟨a,b,hgval⟩ := g.property
  have hg' : g=coordinateElement m a b := Subtype.ext hgval
  have hcomm : ∀ c : Field m,theta m a*c+theta m c*a=0 := by
    intro c
    have he : ⁅g,coordinateElement m c 0⁆=1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        ((Subgroup.mem_center_iff.mp hg (coordinateElement m c 0)).symm)
    rw [hg',coordinateElement_commutator] at he
    have hv := congrArg (fun x : unipotentSubgroup m =>
      (x.val : CFSG.Models.SuzukiConstruction.Mat m) 2 0) he
    exact hv
  have ha : a=0 ∨ a=1 := by
    apply (theta_add_self_eq_zero_iff m a).mp
    simpa only [map_one,mul_one,one_mul] using hcomm 1
  rcases ha with ha|ha
  · rw [hg',coordinateElement_mem_centralParameters]
    exact ha
  · obtain ⟨t,ht⟩ := exists_twist_difference_ne_zero m hm
    have he := hcomm t
    rw [ha,map_one,one_mul,mul_one] at he
    exact False.elim (ht (by simpa only [add_comm] using he))

theorem center_eq_centralParameters (m : ℕ) (hm : 1≤m) :
    Subgroup.center (unipotentSubgroup m)=centralParameters m :=
  le_antisymm (center_le_centralParameters m hm) (centralParameters_le_center m)

theorem commutator_eq_centralParameters (m : ℕ) (hm : 1≤m) :
    commutator (unipotentSubgroup m)=centralParameters m := by
  apply le_antisymm
  · exact Abelianization.commutator_subset_ker (firstParameterHom m)
  · intro g hg
    obtain ⟨a,b,hgval⟩ := g.property
    have hg' : g=coordinateElement m a b := Subtype.ext hgval
    rw [hg',coordinateElement_mem_centralParameters] at hg
    subst a
    obtain ⟨c,d,hcd⟩ := every_central_parameter_is_commutator m hm b
    have he : ⁅coordinateElement m c 0,coordinateElement m d 0⁆=coordinateElement m 0 b :=
      Subtype.ext hcd
    rw [hg',←he]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem commutator_eq_center (m : ℕ) (hm : 1≤m) :
    commutator (unipotentSubgroup m)=Subgroup.center (unipotentSubgroup m) := by
  rw [commutator_eq_centralParameters m hm,center_eq_centralParameters m hm]

/-- The quotient is by the actual first-coordinate kernel, rather than a
subgroup merely having the same cardinality. -/
def firstParameterQuotientEquiv (m : ℕ) :
    (unipotentSubgroup m)⧸centralParameters m≃*Multiplicative (Field m) :=
  QuotientGroup.quotientKerEquivOfSurjective (firstParameterHom m) (firstParameterHom_surjective m)

end SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
