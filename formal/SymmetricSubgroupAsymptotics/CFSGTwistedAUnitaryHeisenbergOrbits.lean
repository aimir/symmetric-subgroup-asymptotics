import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHeisenbergIndex
import SymmetricSubgroupAsymptotics.CFSGCentralTransitiveAction

/-! Exact Heisenberg divisibility on an ACTUAL radical orbit where its
centre acts nontrivially. The centre-orbit count is the index of the
literal vector image of the original point stabilizer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open MulAction

def radicalCentre (q : CFSG.PrimePower) (s : ℕ) : Subgroup (fixedRadical q s) :=
  (fixedRadicalParameterHom q s).ker

theorem radicalCentre_le_center (q : CFSG.PrimePower) (s : ℕ) :
    radicalCentre q s ≤ Subgroup.center (fixedRadical q s) := by
  rw [radicalCentre, ← centralRadicalHom_range_eq_kernel]
  rintro g ⟨c, rfl⟩
  exact centralRadicalHom_mem_center q s c

theorem radicalCentre_card (q : CFSG.PrimePower) (s : ℕ) :
    Nat.card (radicalCentre q s) = q.order := fixedRadicalParameterHom_kernel_card q s

theorem radicalCentralPreimage_index_eq (q : CFSG.PrimePower) (s : ℕ)
    (H : Subgroup (fixedRadical q s)) :
    (radicalCentralPreimage q s H).index = H.relIndex (radicalCentre q s) := by
  change (H.comap (centralRadicalHom q s)).index = _
  rw [Subgroup.index_comap, centralRadicalHom_range_eq_kernel]
  rfl

variable {X : Type*}

theorem radical_central_orbit_count (q : CFSG.PrimePower) (s : ℕ)
    [MulAction (fixedRadical q s) X] [MulAction.IsPretransitive (fixedRadical q s) X]
    [Finite X] (x : X) :
    Nat.card (Quotient (orbitRel (radicalCentre q s) X)) =
      ((stabilizer (fixedRadical q s) x).map (fixedRadicalParameterHom q s)).index := by
  let H := stabilizer (fixedRadical q s) x
  have hh := CFSGCentralTransitiveAction.card_eq_central_orbits_mul_relIndex
    (G := fixedRadical q s) (X := X)
    (radicalCentre q s) (radicalCentre_le_center q s) x
  rw [CFSGCentralTransitiveAction.transitive_card_eq_index (G := fixedRadical q s) (X := X) x,
    radical_subgroup_index_factor q s H, radicalCentralPreimage_index_eq] at hh
  have hp : 0 < H.relIndex (radicalCentre q s) :=
    Nat.card_pos (α := radicalCentre q s ⧸ H.subgroupOf (radicalCentre q s))
  apply Nat.eq_of_mul_eq_mul_left hp
  calc
    H.relIndex (radicalCentre q s) * Nat.card (Quotient (orbitRel (radicalCentre q s) X)) =
        Nat.card (Quotient (orbitRel (radicalCentre q s) X)) * H.relIndex (radicalCentre q s) :=
      Nat.mul_comm _ _
    _ = H.relIndex (radicalCentre q s) * (H.map (fixedRadicalParameterHom q s)).index := hh.symm

theorem radical_transitive_divisibility (q : CFSG.PrimePower) (s : ℕ)
    [MulAction (fixedRadical q s) X] [MulAction.IsPretransitive (fixedRadical q s) X]
    [Finite X] (x : X)
    (hx : ¬ radicalCentre q s ≤ stabilizer (fixedRadical q s) x) :
    q.order ^ (s + 1) ∣ Nat.card X := by
  have hH : ¬ (centralRadicalHom q s).range ≤ stabilizer (fixedRadical q s) x := by
    rw [centralRadicalHom_range_eq_kernel]
    exact hx
  obtain ⟨m, hm⟩ := radical_subgroup_index_central_divisibility q s
    (stabilizer (fixedRadical q s) x) hH
  rw [CFSGCentralTransitiveAction.transitive_card_eq_index (G := fixedRadical q s) (X := X) x, hm]
  refine ⟨(radicalCentralPreimage q s (stabilizer (fixedRadical q s) x)).index * m, ?_⟩
  ring

theorem radical_transitive_orbit_divisibility (q : CFSG.PrimePower) (s : ℕ)
    [MulAction (fixedRadical q s) X] [MulAction.IsPretransitive (fixedRadical q s) X]
    [Finite X] (x : X)
    (hx : ¬ radicalCentre q s ≤ stabilizer (fixedRadical q s) x) :
    q.order ^ (s + 1) ∣ Nat.card (Quotient (orbitRel (radicalCentre q s) X)) := by
  rw [radical_central_orbit_count (X := X) q s x]
  apply radicalVectorImage_index_dvd q s
  rw [centralRadicalHom_range_eq_kernel]
  exact hx

theorem radical_transitive_fixedBy_divisibility (q : CFSG.PrimePower) (s : ℕ)
    [MulAction (fixedRadical q s) X] [MulAction.IsPretransitive (fixedRadical q s) X]
    [Finite X] (x : X)
    (hx : ¬ radicalCentre q s ≤ stabilizer (fixedRadical q s) x)
    (c : radicalCentre q s) : q.order ^ (s + 1) ∣ Nat.card (fixedBy X c) := by
  rcases CFSGCentralTransitiveAction.central_fixedBy_eq_univ_or_empty
    (G := fixedRadical q s) (X := X)
    (radicalCentre q s) (radicalCentre_le_center q s) c with he | he
  · rw [he, Nat.card_univ]
    exact radical_transitive_divisibility q s x hx
  · rw [he]
    simp

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
