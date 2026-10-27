import SymmetricSubgroupAsymptotics.SimpleProductAxisStabilizerRestriction

/-! The restriction is applied to the actual original point stabilizer through
one fixed genuine chart of the normal subgroup. No independent coordinate
stabilizers or faithful product action are postulated. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ActualNormalSimpleProductStabilizerRestriction
open SimpleProductAxisStabilizerRestriction
variable {G X J T : Type} [Group G] [Finite G] [Finite X]
  [MulAction G X] [MulAction.IsPretransitive G X]
  [Group T] [Finite T] [IsSimpleGroup T] [Fintype J] [DecidableEq J]

abbrev chartStabilizer (L : Subgroup G) (e : L ≃* (J → T)) (x : X) :
    Subgroup (J → T) := (MulAction.stabilizer L x).map e.toMonoidHom

abbrev actualAxis (L : Subgroup G) (e : L ≃* (J → T)) (i : J) : T →* G :=
  L.subtype.comp (e.symm.toMonoidHom.comp (axis i))

theorem chart_stabilizer_index_dvd (L : Subgroup G) [L.Normal]
    (e : L ≃* (J → T)) (x : X) (m : ℕ) (hdegree : Nat.card X ∣ 3*2^m) :
    (chartStabilizer L e x).index ∣ 3*2^m := by
  have he : (chartStabilizer L e x).index=(MulAction.stabilizer L x).index :=
    (MulAction.stabilizer L x).index_map_equiv e
  rw [he,MulAction.index_stabilizer]
  exact ((MulAction.IsBlock.orbit_of_normal (N:=L) x).ncard_dvd_card
    ⟨x,MulAction.mem_orbit_self x⟩).trans hdegree

/-- Every actual axis moving the original point has proper projection of the
same actual charted stabilizer. Inactive axes are deliberately retained. -/
theorem projection_ne_top_of_actual_movement (L : Subgroup G) [L.Normal]
    (e : L ≃* (J → T)) (hn : ¬IsMulCommutative T)
    (x : X) (m : ℕ) (hdegree : Nat.card X ∣ 3*2^m) (i : J)
    (hmove : ∃ t : T,actualAxis L e i t • x ≠ x) :
    (chartStabilizer L e x).map (coordinate i) ≠ ⊤ := by
  apply projection_ne_top_of_active hn (chartStabilizer L e x) i m
    (chart_stabilizer_index_dvd L e x m hdegree)
  intro hle
  obtain ⟨t,ht⟩ := hmove
  have hm : axis i t ∈ chartStabilizer L e x := hle ⟨t,rfl⟩
  obtain ⟨l,hl,he⟩ := hm
  have hel : l=e.symm (axis i t) := e.injective (by simpa using he)
  rw [hel] at hl
  exact ht hl

/-- This is the genuine simple-subgroup index menu on each active original axis. -/
theorem active_projection_proper_and_index_dvd (L : Subgroup G) [L.Normal]
    (e : L ≃* (J → T)) (hn : ¬IsMulCommutative T)
    (x : X) (m : ℕ) (hdegree : Nat.card X ∣ 3*2^m) (i : J)
    (hmove : ∃ t : T,actualAxis L e i t • x ≠ x) :
    (chartStabilizer L e x).map (coordinate i) ≠ ⊤ ∧
      ((chartStabilizer L e x).map (coordinate i)).index ∣ 3*2^m := by
  exact ⟨projection_ne_top_of_actual_movement L e hn x m hdegree i hmove,
    (projection_index_dvd_index (chartStabilizer L e x) i).trans
      (chart_stabilizer_index_dvd L e x m hdegree)⟩

end SymmetricSubgroupAsymptotics.ActualNormalSimpleProductStabilizerRestriction
