import SymmetricSubgroupAsymptotics.PrimitiveAlternatingSharpSubnormalPartitionWreath
import SymmetricSubgroupAsymptotics.AlmostSimpleIndexTwoSubnormalClasses

/-! Natural-degree alternating recognition on the ACTUAL coordinate
set. A single socle factor of order m!/2 in degree m forces the original
permutation subgroup to contain the literal alternating group by index
two. No permutation-representation equivalence is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveAlternatingNaturalDegreeRecognition
open PrimitiveSocleRawStructure

private theorem alternating_or_top_of_card_lower
    (X : Type) [Fintype X] [DecidableEq X] [Nontrivial X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Nat.card (alternatingGroup X) ≤ Nat.card P) :
    P=alternatingGroup X ∨ P=⊤ := by
  have hindex : P.index ≤ 2 := by
    have hmul : P.index*Nat.card P ≤ 2*Nat.card P := by
      calc
        P.index*Nat.card P = Nat.card (Equiv.Perm X) := P.index_mul_card
        _ = 2*Nat.card (alternatingGroup X) := two_mul_nat_card_alternatingGroup.symm
        _ ≤ 2*Nat.card P := Nat.mul_le_mul_left _ hcard
    exact Nat.le_of_mul_le_mul_right hmul (Nat.card_pos (α := P))
  exact AlmostSimpleIndexTwoSubnormalClasses.containing_simple_index_two
    (alternatingGroup X) P alternatingGroup.index_eq_two
    (Equiv.Perm.alternatingGroup_le_of_index_le_two hindex)

theorem alternating_or_top_of_single_factor_natural_degree
    {X : Type} [Finite X] (P : Subgroup (Equiv.Perm X))
    (D : NonaffineData P X) (m : ℕ) (hm : 5 ≤ m)
    (e : D.Simple ≃* alternatingGroup (Fin m))
    (hk : D.factorCount=1) (hdegree : Nat.card X=m) :
    letI := Fintype.ofFinite X
    letI := Classical.decEq X
    P=alternatingGroup X ∨ P=⊤ := by
  letI := Fintype.ofFinite X
  letI := Classical.decEq X
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  letI : Nontrivial (Fin m) := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_fin] using (show 1 < m by omega))
  have hsoc : Nat.card (finiteGroupSocle P)=Nat.card D.Simple := by
    rw [Nat.card_congr D.socleEquiv.toEquiv,Nat.card_fun,Nat.card_fin,hk,pow_one]
  have he : Nat.card D.Simple=Nat.card (alternatingGroup (Fin m)) := Nat.card_congr e.toEquiv
  have hx : 2*Nat.card (alternatingGroup X)=m.factorial := by
    simpa only [Nat.card_perm,hdegree] using (two_mul_nat_card_alternatingGroup (α := X))
  have hmcard : 2*Nat.card (alternatingGroup (Fin m))=m.factorial := by
    simpa only [Nat.card_perm,Nat.card_fin] using (two_mul_nat_card_alternatingGroup (α := Fin m))
  have hsame : Nat.card D.Simple=Nat.card (alternatingGroup X) := by omega
  have hsub : Nat.card (finiteGroupSocle P) ≤ Nat.card P :=
    Nat.card_le_card_of_injective (finiteGroupSocle P).subtype Subtype.val_injective
  rw [hsoc,hsame] at hsub
  exact alternating_or_top_of_card_lower X P hsub

end SymmetricSubgroupAsymptotics.PrimitiveAlternatingNaturalDegreeRecognition
