import SymmetricSubgroupAsymptotics.DerivedWordFiniteCertificate
import SymmetricSubgroupAsymptotics.GeneratedAction16.DataChunk027

/-! Selected 16-row certificate for the derived subgroup of the literal
16T1083 action. Displayed original derived words generate the candidate;
all transitions, conjugates and original commutators are checked on the
sixteen original points. No ambient-group enumeration is imported. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.BinaryCarrierDerivedOrder16T1083

abbrev Original :=
  Subgroup.closure (Set.range BinaryActionData16.node1083Generators)

def basisWords : Fin 4 → DerivedGeneratorWord (Fin 7) :=
  ![.comm 0 6, .comm 1 2, .comm 1 5, .comm 2 4]

private def ambientBasis (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (basisWords j).eval BinaryActionData16.node1083Generators

private def rowWords (i : Fin 16) : List (Fin 4) :=
  ![[], [0], [1], [2], [3], [0,1], [0,2], [0,3],
    [1,2], [1,3], [2,3], [0,1,2], [0,1,3], [0,2,3], [1,2,3], [0,1,2,3]] i

def ambientRows (i : Fin 16) : Equiv.Perm (Fin 16) :=
  ((rowWords i).map ambientBasis).prod

private def elements (i : Fin 16) : Original :=
  ((rowWords i).map
    (derivedWordGenerators BinaryActionData16.node1083Generators basisWords)).prod

private theorem basis_coe (j : Fin 4) :
    (derivedWordGenerators BinaryActionData16.node1083Generators basisWords j :
      Equiv.Perm (Fin 16)) = ambientBasis j :=
  closureGenerators_eval_coe BinaryActionData16.node1083Generators (basisWords j)

private theorem elements_coe (i : Fin 16) :
    (elements i : Equiv.Perm (Fin 16)) = ambientRows i := by
  change Original.subtype (((rowWords i).map
    (derivedWordGenerators BinaryActionData16.node1083Generators basisWords)).prod) = _
  have hf : Original.subtype ∘
      derivedWordGenerators BinaryActionData16.node1083Generators basisWords = ambientBasis := by
    funext j
    exact basis_coe j
  rw [map_list_prod, List.map_map, hf]
  rfl

private def next (i : Fin 16) (j : Fin 4) : Fin 16 :=
  ![![1,2,3,4], ![0,5,6,7], ![5,0,8,9], ![6,8,0,10],
    ![7,9,10,0], ![2,1,11,12], ![3,11,1,13], ![4,12,13,1],
    ![11,3,2,14], ![12,4,14,2], ![13,14,4,3], ![8,6,5,15],
    ![9,7,15,5], ![10,15,7,6], ![15,10,9,8], ![14,13,12,11]] i j

private def conjugateRow (i : Fin 7) (j : Fin 4) : Fin 16 :=
  ![![1,2,3,4], ![1,2,3,4], ![1,2,6,4],
    ![1,2,3,4], ![1,2,3,4], ![1,5,3,4],
    ![1,5,6,7]] i j

private def commutatorRow (i j : Fin 7) : Fin 16 :=
  ![![0,0,0,0,0,0,1], ![0,0,2,0,0,3,8], ![0,2,0,0,4,5,4],
    ![0,0,0,0,0,4,9], ![0,0,4,0,0,4,11], ![0,3,5,4,4,0,6],
    ![1,8,4,9,11,6,0]] i j

private theorem identity_pointwise : ∀ x : Fin 16, ambientRows 0 x = x := by
  decide +kernel

private theorem next_pointwise : ∀ (i : Fin 16) (j : Fin 4) (x : Fin 16),
    ambientRows (next i j) x = (ambientRows i * ambientBasis j) x := by
  decide +kernel

private theorem conjugate_pointwise : ∀ (i : Fin 7) (j : Fin 4) (x : Fin 16),
    ambientRows (conjugateRow i j) x =
      (BinaryActionData16.node1083Generators i * ambientBasis j *
        (BinaryActionData16.node1083Generators i)⁻¹) x := by
  decide +kernel

private theorem commutator_pointwise : ∀ (i j : Fin 7) (x : Fin 16),
    ambientRows (commutatorRow i j) x =
      ⁅BinaryActionData16.node1083Generators i,
        BinaryActionData16.node1083Generators j⁆ x := by
  decide +kernel

private theorem pointwise_rows_injective : ∀ i j : Fin 16,
    (∀ x : Fin 16, ambientRows i x = ambientRows j x) → i = j := by
  decide +kernel

private def cayley : FiniteCayleyCertificate
    (derivedWordGenerators BinaryActionData16.node1083Generators basisWords) 16 where
  elements := elements
  identity := 0
  identity_eq := by
    apply Subtype.ext
    change (elements 0 : Equiv.Perm (Fin 16)) = 1
    rw [elements_coe]
    exact Equiv.ext identity_pointwise
  next := next
  next_eq := by
    intro i j
    apply Subtype.ext
    change (elements (next i j) : Equiv.Perm (Fin 16)) =
      (elements i : Equiv.Perm (Fin 16)) *
        (derivedWordGenerators BinaryActionData16.node1083Generators basisWords j :
          Equiv.Perm (Fin 16))
    rw [elements_coe, elements_coe, basis_coe]
    exact Equiv.ext (next_pointwise i j)
  words := rowWords
  words_eq _ := rfl

/-- Every row equation is on the same original action and the same displayed
derived words. The generic consumer supplies all derived-group reasoning. -/
def certificate : DerivedWordFiniteCertificate
    BinaryActionData16.node1083Generators basisWords 16 where
  cayley := cayley
  rows_injective := by
    intro i j h
    have he : (elements i : Equiv.Perm (Fin 16)) =
        (elements j : Equiv.Perm (Fin 16)) := congrArg Subtype.val h
    rw [elements_coe, elements_coe] at he
    exact pointwise_rows_injective i j (fun x => congrArg (fun f => f x) he)
  conjugateRow := conjugateRow
  conjugate_eq := by
    intro i j
    apply Subtype.ext
    change (elements (conjugateRow i j) : Equiv.Perm (Fin 16)) =
      BinaryActionData16.node1083Generators i *
        (derivedWordGenerators BinaryActionData16.node1083Generators basisWords j :
          Equiv.Perm (Fin 16)) * (BinaryActionData16.node1083Generators i)⁻¹
    rw [elements_coe, basis_coe]
    exact Equiv.ext (conjugate_pointwise i j)
  commutatorRow := commutatorRow
  commutator_eq := by
    intro i j
    apply Subtype.ext
    change (elements (commutatorRow i j) : Equiv.Perm (Fin 16)) =
      ⁅BinaryActionData16.node1083Generators i, BinaryActionData16.node1083Generators j⁆
    rw [elements_coe]
    exact Equiv.ext (commutator_pointwise i j)

/-- Public literal row binding for subsequent original-point centralizer checks. -/
theorem certificate_elements_coe (i : Fin 16) :
    (certificate.cayley.elements i : Equiv.Perm (Fin 16)) = ambientRows i :=
  elements_coe i

theorem card_commutator : Nat.card (commutator Original) = 16 :=
  certificate.card_commutator

private theorem noncentral_point :
    (BinaryActionData16.node1083Generators 5 * ambientBasis 1 *
      (BinaryActionData16.node1083Generators 5)⁻¹) (0 : Fin 16) ≠
        ambientBasis 1 (0 : Fin 16) := by
  decide +kernel

/-- A displayed original conjugation moves a displayed derived element.
This is whole-original-group noncentrality, not internal noncommutativity. -/
theorem commutator_not_le_center : ¬ commutator Original ≤ Subgroup.center Original := by
  intro h
  let d : Original := derivedWordGenerators BinaryActionData16.node1083Generators basisWords 1
  let u : Original := closureGenerators BinaryActionData16.node1083Generators 5
  have hd : d ∈ commutator Original :=
    (basisWords 1).eval_mem_commutator (closureGenerators BinaryActionData16.node1083Generators)
  have he : u * d = d * u := Subgroup.mem_center_iff.mp (h hd) u
  have hc : u * d * u⁻¹ = d := by
    rw [he, mul_assoc, mul_inv_cancel, mul_one]
  have hp := congrArg Subtype.val hc
  change BinaryActionData16.node1083Generators 5 *
    (derivedWordGenerators BinaryActionData16.node1083Generators basisWords 1 :
      Equiv.Perm (Fin 16)) * (BinaryActionData16.node1083Generators 5)⁻¹ =
    (derivedWordGenerators BinaryActionData16.node1083Generators basisWords 1 :
      Equiv.Perm (Fin 16)) at hp
  rw [basis_coe] at hp
  exact noncentral_point (congrArg (fun f : Equiv.Perm (Fin 16) => f 0) hp)

end SymmetricSubgroupAsymptotics.BinaryCarrierDerivedOrder16T1083
