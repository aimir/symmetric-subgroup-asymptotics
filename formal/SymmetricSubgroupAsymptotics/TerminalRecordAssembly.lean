import SymmetricSubgroupAsymptotics.TerminalRecords
import SymmetricSubgroupAsymptotics.TerminalGraphClassification

/-!
# Terminal records on the complete original exterior

Every linear record gives a faithful map from its ordered vertical kernel
times the complete group T. Its literal image is the classified quotient
graph. Thus arbitrary weights on that image retain the original record divisor.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {T V : Type*} [Group T] [AddCommGroup V] [Module (ZMod 2) V]

/-- The original group map associated to a quotient record. -/
def terminalRecordGroupMap (U : Submodule (ZMod 2) V)
    (f : BinaryAbelianization T →ₗ[ZMod 2] V ⧸ U)
    (p : TerminalRecordMaps U f) :
    (Multiplicative (Fin (Module.finrank (ZMod 2) U) → ZMod 2) × T) →*
      (Multiplicative V × T) where
  toFun x := (Multiplicative.ofAdd
    (p.1 (x.1.toAdd,binaryAbelianizationMap T (Additive.ofMul x.2))),x.2)
  map_one' := by
    apply Prod.ext
    · change Multiplicative.ofAdd (p.1 (0,binaryAbelianizationMap T 0)) = 1
      simp
      exact p.1.map_zero
    · rfl
  map_mul' x y := by
    apply Prod.ext
    · change Multiplicative.ofAdd (p.1 (x.1.toAdd + y.1.toAdd,
        binaryAbelianizationMap T (Additive.ofMul x.2 + Additive.ofMul y.2))) = _
      rw [map_add]
      change Multiplicative.ofAdd (p.1
        ((x.1.toAdd,binaryAbelianizationMap T (Additive.ofMul x.2)) +
          (y.1.toAdd,binaryAbelianizationMap T (Additive.ofMul y.2)))) = _
      rw [map_add]
      rfl
    · rfl

/-- The record's image is the actual subgroup of V×T, with every internal
relation of T retained. -/
theorem terminalRecordGroupMap_range (U : Submodule (ZMod 2) V)
    (f : BinaryAbelianization T →ₗ[ZMod 2] V ⧸ U)
    (p : TerminalRecordMaps U f) :
    (terminalRecordGroupMap U f p).range = terminalLinearQuotientGraph U f := by
  ext x
  rw [mem_terminalLinearQuotientGraph]
  have he := terminalRecordMaps_image U f p
  constructor
  · rintro ⟨⟨b,t⟩,rfl⟩
    have hm :
        (p.1 (b.toAdd,binaryAbelianizationMap T (Additive.ofMul t)),
          binaryAbelianizationMap T (Additive.ofMul t)) ∈ terminalLinearGraph U f := by
      exact he.le ⟨(b.toAdd,binaryAbelianizationMap T (Additive.ofMul t)),rfl⟩
    exact ((mem_terminalLinearGraph U f _).mp hm).symm
  · intro hx
    have hm : (x.1.toAdd,binaryAbelianizationMap T (Additive.ofMul x.2)) ∈
        terminalLinearGraph U f := (mem_terminalLinearGraph U f _).mpr hx.symm
    obtain ⟨⟨b,a⟩,ha⟩ := he.ge hm
    have hfirst := congrArg Prod.fst ha
    have hsecond := congrArg Prod.snd ha
    change a = binaryAbelianizationMap T (Additive.ofMul x.2) at hsecond
    subst a
    refine ⟨(Multiplicative.ofAdd b,x.2),?_⟩
    apply Prod.ext
    · exact congrArg Multiplicative.ofAdd hfirst
    · rfl

/-- Choosing a lift and an ordered vertical basis gives an isomorphism onto
the actual image, not an extra extension fibre. -/
theorem terminalRecordGroupMap_injective (U : Submodule (ZMod 2) V)
    (f : BinaryAbelianization T →ₗ[ZMod 2] V ⧸ U)
    (p : TerminalRecordMaps U f) : Function.Injective (terminalRecordGroupMap U f p) := by
  rintro ⟨b,t⟩ ⟨c,s⟩ h
  have hts : t = s := congrArg Prod.snd h
  subst s
  apply Prod.ext
  · apply Multiplicative.toAdd.injective
    apply p.2.1
    have hp := congrArg (fun x : Multiplicative V × T ↦ x.1.toAdd) h
    change p.1 (b.toAdd,binaryAbelianizationMap T (Additive.ofMul t)) =
      p.1 (c.toAdd,binaryAbelianizationMap T (Additive.ofMul t)) at hp
    have hb : (b.toAdd,binaryAbelianizationMap T (Additive.ofMul t)) =
        (b.toAdd,0) + (0,binaryAbelianizationMap T (Additive.ofMul t)) := by simp
    have hc : (c.toAdd,binaryAbelianizationMap T (Additive.ofMul t)) =
        (c.toAdd,0) + (0,binaryAbelianizationMap T (Additive.ofMul t)) := by simp
    rw [hb,hc,map_add,map_add,add_right_cancel_iff] at hp
    exact hp
  · rfl

/-- Specialization of the exact divisor to the complete exterior's actual
binary character rank. -/
theorem terminalActualRecords_card [Finite T] [Finite V]
    (U : Submodule (ZMod 2) V)
    (f : BinaryAbelianization T →ₗ[ZMod 2] V ⧸ U) :
    Nat.card (TerminalRecordMaps U f) =
      (∏ i : Fin (Module.finrank (ZMod 2) U),
        (2 ^ Module.finrank (ZMod 2) U - 2 ^ (i : ℕ))) *
      2 ^ (Module.finrank (ZMod 2) U * binaryCharacterRank T) := by
  rw [terminalRecordMaps_card,binaryAbelianization_finrank]

/-- Any original image weight retains the exact record divisor. This
includes a weight defined from the central extension's full H² annihilator. -/
theorem terminalActualRecords_weight_sum [Finite T] [Finite V]
    (U : Submodule (ZMod 2) V)
    (f : BinaryAbelianization T →ₗ[ZMod 2] V ⧸ U)
    {M : Type*} [AddCommMonoid M] (w : Subgroup (Multiplicative V × T) → M) :
    letI := Fintype.ofFinite (TerminalRecordMaps U f)
    (∑ p : TerminalRecordMaps U f, w (terminalRecordGroupMap U f p).range) =
      ((∏ i : Fin (Module.finrank (ZMod 2) U),
        (2 ^ Module.finrank (ZMod 2) U - 2 ^ (i : ℕ))) *
        2 ^ (Module.finrank (ZMod 2) U * binaryCharacterRank T)) •
        w (terminalLinearQuotientGraph U f) := by
  classical
  letI := Fintype.ofFinite (TerminalRecordMaps U f)
  simp only [terminalRecordGroupMap_range,Finset.sum_const,Finset.card_univ,
    ← Nat.card_eq_fintype_card,terminalActualRecords_card]

end SymmetricSubgroupAsymptotics
