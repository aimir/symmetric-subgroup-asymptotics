import SymmetricSubgroupAsymptotics.BinaryPairFrameSignIsotypes
import SymmetricSubgroupAsymptotics.SylowPrimePowerTransitive

/-!
# The actual top action on literal sign isotypes

The equality classes of the pair-kernel characters carry an action of the
original pair group.  The stabilizer of one such class acts transitively on
the coordinates which carry that character.  Consequently a character
fibre of binary prime-power size has a transitive binary subgroup inside
its literal stabilizer.

This is the group-theoretic input for the high-isotype signed-module
argument at six and twelve pair coordinates.  It is completely generic in
the pair frame and does not choose a transitive-group catalogue row.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryPairFrame

variable {X I : Type*} {G : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame G I)

/-- A chosen coordinate carrying a realized literal sign. -/
noncomputable def coordinateSignRepresentative
    (chi : CoordinateSign F) : I :=
  Classical.choose chi.2

theorem coordinateSignRepresentative_spec
    (chi : CoordinateSign F) :
    coordinateSign F (coordinateSignRepresentative F chi) = chi := by
  apply Subtype.ext
  exact Classical.choose_spec chi.2

/-- Transport a realized sign by an element of the actual pair action. -/
noncomputable def coordinateSignTopMap
    (u : G) (chi : CoordinateSign F) : CoordinateSign F :=
  coordinateSign F (F.top u (coordinateSignRepresentative F chi))

@[simp] theorem coordinateSignTopMap_apply_coordinate
    (u : G) (i : I) :
    coordinateSignTopMap F u (coordinateSign F i) =
      coordinateSign F (F.top u i) := by
  apply (coordinateSign_top_eq_iff F u _ _).2
  exact coordinateSignRepresentative_spec F (coordinateSign F i)

@[simp] theorem coordinateSignTopMap_one
    (chi : CoordinateSign F) :
    coordinateSignTopMap F 1 chi = chi := by
  obtain ⟨i, rfl⟩ := coordinateSign_surjective F chi
  simp only [coordinateSignTopMap_apply_coordinate, map_one,
    Equiv.Perm.one_apply]

theorem coordinateSignTopMap_mul
    (u v : G) (chi : CoordinateSign F) :
    coordinateSignTopMap F (u * v) chi =
      coordinateSignTopMap F u (coordinateSignTopMap F v chi) := by
  obtain ⟨i, rfl⟩ := coordinateSign_surjective F chi
  simp only [coordinateSignTopMap_apply_coordinate, map_mul,
    Equiv.Perm.mul_apply]

/-- The actual pair action on its realized sign classes. -/
noncomputable def coordinateSignTopPerm
    (u : G) : Equiv.Perm (CoordinateSign F) where
  toFun := coordinateSignTopMap F u
  invFun := coordinateSignTopMap F u⁻¹
  left_inv chi := by
    rw [← coordinateSignTopMap_mul]
    simp
  right_inv chi := by
    rw [← coordinateSignTopMap_mul]
    simp

@[simp] theorem coordinateSignTopPerm_apply
    (u : G) (chi : CoordinateSign F) :
    coordinateSignTopPerm F u chi = coordinateSignTopMap F u chi :=
  rfl

/-- The induced action on the literal sign classes. -/
noncomputable def coordinateSignTopHom :
    G →* Equiv.Perm (CoordinateSign F) where
  toFun := coordinateSignTopPerm F
  map_one' := by
    apply Equiv.ext
    exact coordinateSignTopMap_one F
  map_mul' u v := by
    apply Equiv.ext
    exact coordinateSignTopMap_mul F u v

@[simp] theorem coordinateSignTopHom_apply_coordinate
    (u : G) (i : I) :
    coordinateSignTopHom F u (coordinateSign F i) =
      coordinateSign F (F.top u i) :=
  coordinateSignTopMap_apply_coordinate F u i

/-- The canonical action of the pair group on its realized signs. -/
noncomputable instance coordinateSignMulAction :
    MulAction G (CoordinateSign F) :=
  MulAction.compHom (CoordinateSign F) (coordinateSignTopHom F)

@[simp] theorem smul_coordinateSign
    (u : G) (i : I) :
    u • coordinateSign F i = coordinateSign F (F.top u i) :=
  coordinateSignTopHom_apply_coordinate F u i

/-- The stabilizer of one sign class acts on the coordinates in that
literal character fibre. -/
noncomputable def coordinateSignFiberTopPerm
    (chi : CoordinateSign F)
    (u : MulAction.stabilizer G chi) :
    Equiv.Perm {i : I // coordinateSign F i = chi} where
  toFun i := ⟨F.top u.1 i.1, by
    rw [← smul_coordinateSign F, i.2]
    exact MulAction.mem_stabilizer_iff.mp u.2⟩
  invFun i := ⟨F.top u.1⁻¹ i.1, by
    rw [← smul_coordinateSign F, i.2]
    have hu : u.1 • chi = chi := MulAction.mem_stabilizer_iff.mp u.2
    calc
      u.1⁻¹ • chi = u.1⁻¹ • (u.1 • chi) := congrArg (u.1⁻¹ • ·) hu.symm
      _ = chi := inv_smul_smul u.1 chi⟩
  left_inv i := by
    apply Subtype.ext
    exact (F.top u.1).symm_apply_apply i.1
  right_inv i := by
    apply Subtype.ext
    exact (F.top u.1).apply_symm_apply i.1

@[simp] theorem coordinateSignFiberTopPerm_apply
    (chi : CoordinateSign F)
    (u : MulAction.stabilizer G chi)
    (i : {i : I // coordinateSign F i = chi}) :
    (coordinateSignFiberTopPerm F chi u i).1 = F.top u.1 i.1 :=
  rfl

/-- The literal stabilizer action on one sign fibre. -/
noncomputable def coordinateSignFiberTopHom
    (chi : CoordinateSign F) :
    MulAction.stabilizer G chi →*
      Equiv.Perm {i : I // coordinateSign F i = chi} where
  toFun := coordinateSignFiberTopPerm F chi
  map_one' := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    simp
  map_mul' u v := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    simp only [coordinateSignFiberTopPerm_apply, Subgroup.coe_mul,
      map_mul, Equiv.Perm.mul_apply]

/-- The canonical action of a sign stabilizer on its coordinate fibre. -/
noncomputable instance coordinateSignFiberMulAction
    (chi : CoordinateSign F) :
    MulAction (MulAction.stabilizer G chi)
      {i : I // coordinateSign F i = chi} :=
  MulAction.compHom _ (coordinateSignFiberTopHom F chi)

/-- Transitivity of the physical pair action makes the stabilizer of a
realized sign transitive on all coordinates carrying that sign. -/
theorem coordinateSignFiber_stabilizer_pretransitive
    (htrans : MulAction.IsPretransitive G X)
    (chi : CoordinateSign F) :
    MulAction.IsPretransitive (MulAction.stabilizer G chi)
      {i : I // coordinateSign F i = chi} := by
  letI : MulAction.IsPretransitive G X := htrans
  letI : MulAction.IsPretransitive F.top.range I := F.top_pretransitive
  constructor
  intro i j
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq F.top.range i.1 j.1
  obtain ⟨u, rfl⟩ := F.top.rangeRestrict_surjective t
  have htop : F.top u i.1 = j.1 := by simpa using ht
  have hsign : u • chi = chi := by
    calc
      u • chi = u • coordinateSign F i.1 := congrArg (u • ·) i.2.symm
      _ = coordinateSign F (F.top u i.1) := smul_coordinateSign F u i.1
      _ = coordinateSign F j.1 := congrArg (coordinateSign F) htop
      _ = chi := j.2
  let us : MulAction.stabilizer G chi :=
    ⟨u, MulAction.mem_stabilizer_iff.mpr hsign⟩
  refine ⟨us, ?_⟩
  apply Subtype.ext
  exact htop

/-- If one literal sign fibre has binary prime-power size, its actual sign
stabilizer contains a transitive binary subgroup. -/
theorem exists_transitive_binarySubgroup_of_coordinateSignFiber
    [Finite X] [Finite I]
    (htrans : MulAction.IsPretransitive G X)
    (chi : CoordinateSign F) (a : ℕ)
    (hcard : Nat.card {i : I // coordinateSign F i = chi} = 2 ^ a) :
    ∃ P : Subgroup (MulAction.stabilizer G chi),
      IsPGroup 2 P ∧
      MulAction.IsPretransitive P
        {i : I // coordinateSign F i = chi} := by
  letI : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
  letI : MulAction.IsPretransitive (MulAction.stabilizer G chi)
      {i : I // coordinateSign F i = chi} :=
    coordinateSignFiber_stabilizer_pretransitive F htrans chi
  have hnonempty : Nonempty {i : I // coordinateSign F i = chi} := by
    obtain ⟨i, hi⟩ := coordinateSign_surjective F chi
    exact ⟨⟨i, hi⟩⟩
  letI : Nonempty {i : I // coordinateSign F i = chi} := hnonempty
  let P : Sylow 2 (MulAction.stabilizer G chi) := Classical.choice inferInstance
  have hPtrans : MulAction.IsPretransitive P
      {i : I // coordinateSign F i = chi} :=
    sylow_isPretransitive_of_card_eq_prime_pow P hcard
  exact ⟨P, P.isPGroup', hPtrans⟩

end BinaryPairFrame
end SymmetricSubgroupAsymptotics

end
