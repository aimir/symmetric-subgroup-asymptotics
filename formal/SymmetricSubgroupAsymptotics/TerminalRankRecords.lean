import SymmetricSubgroupAsymptotics.TerminalRecordAssembly
import SymmetricSubgroupAsymptotics.BinaryRankSums

/-! Exact original-record multiplicities with a fixed vertical rank. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

attribute [local instance] Fintype.ofFinite

variable {A V : Type*} [AddCommGroup A] [Module (ZMod 2) A]
  [AddCommGroup V] [Module (ZMod 2) V]

local instance [Finite A] [Finite V] : Finite (A →ₗ[ZMod 2] V) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

/-- Literal ordered records before assigning their unique vertical space. -/
abbrev TerminalOrderedMaps (u : ℕ) :=
  {p : ((Fin u → ZMod 2) × A) →ₗ[ZMod 2] V //
    Function.Injective (p.comp (LinearMap.inl _ _ _))}

/-- The records above one fixed graph, with a separately specified rank. -/
abbrev TerminalRankRecordMaps (u : ℕ) (U : Submodule (ZMod 2) V)
    (f : A →ₗ[ZMod 2] V ⧸ U) :=
  {p : ((Fin u → ZMod 2) × A) →ₗ[ZMod 2] V //
    Function.Injective (p.comp (LinearMap.inl _ _ _)) ∧
    (p.comp (LinearMap.inl _ _ _)).range=U ∧
    U.mkQ.comp (p.comp (LinearMap.inr _ _ _))=f}

/-- The original divisor contains every ordered basis and every lift. -/
def terminalRecordDivisor (u d : ℕ) : ℕ :=
  (∏ i : Fin u, (2^u-2^(i : ℕ))) * 2^(u*d)

theorem terminalRankRecordMaps_card [Finite A] [Finite V] (u : ℕ)
    (U : Submodule (ZMod 2) V) (hU : Module.finrank (ZMod 2) U=u)
    (f : A →ₗ[ZMod 2] V ⧸ U) :
    Nat.card (TerminalRankRecordMaps u U f) =
      terminalRecordDivisor u (Module.finrank (ZMod 2) A) := by
  subst u
  exact terminalRecordMaps_card U f

private def terminalRankRecordsForget (u : ℕ) :
    (Σ U : {U : Submodule (ZMod 2) V // Module.finrank (ZMod 2) U=u},
      Σ f : A →ₗ[ZMod 2] V ⧸ U.1, TerminalRankRecordMaps u U.1 f) →
        TerminalOrderedMaps (A := A) (V := V) u :=
  fun z => ⟨z.2.2.1,z.2.2.2.1⟩

private theorem terminalRankRecordsForget_bijective (u : ℕ) :
    Function.Bijective (terminalRankRecordsForget (A := A) (V := V) u) := by
  constructor
  · rintro ⟨U,f,p⟩ ⟨U',f',p'⟩ h
    have hp : p.1=p'.1 := congrArg Subtype.val h
    have hU : U=U' := by
      apply Subtype.ext
      rw [← p.2.2.1,← p'.2.2.1,hp]
    subst U'
    have hf : f=f' := by rw [← p.2.2.2,← p'.2.2.2,hp]
    subst f'
    have hpp : p=p' := Subtype.ext hp
    subst p'
    rfl
  · intro p
    let U := (p.1.comp (LinearMap.inl _ _ _)).range
    have hU : Module.finrank (ZMod 2) U=u := by
      simpa using LinearMap.finrank_range_of_inj p.2
    exact ⟨⟨⟨U,hU⟩,U.mkQ.comp (p.1.comp (LinearMap.inr _ _ _)),
      ⟨p.1,p.2,rfl,rfl⟩⟩,rfl⟩

/-- Every ordered map has exactly one original vertical space and quotient
graph; this equivalence identifies no distinct ordered records. -/
def terminalRankRecordsEquiv (u : ℕ) :
    (Σ U : {U : Submodule (ZMod 2) V // Module.finrank (ZMod 2) U=u},
      Σ f : A →ₗ[ZMod 2] V ⧸ U.1, TerminalRankRecordMaps u U.1 f) ≃
        TerminalOrderedMaps (A := A) (V := V) u :=
  Equiv.ofBijective _ (terminalRankRecordsForget_bijective u)

section Groups
variable {T : Type*} [Group T]

/-- The raw ordered record map on the complete exterior; injectivity is a
separate property of its vertical restriction. -/
def terminalRawRecordGroupMap (u : ℕ)
    (p : ((Fin u → ZMod 2) × BinaryAbelianization T) →ₗ[ZMod 2] V) :
    Multiplicative (Fin u → ZMod 2) × T →* Multiplicative V × T where
  toFun x := (Multiplicative.ofAdd
    (p (x.1.toAdd,binaryAbelianizationMap T (Additive.ofMul x.2))),x.2)
  map_one' := by
    apply Prod.ext
    · change Multiplicative.ofAdd (p (0,binaryAbelianizationMap T 0))=1
      simp
      exact p.map_zero
    · rfl
  map_mul' x y := by
    apply Prod.ext
    · change Multiplicative.ofAdd (p (x.1.toAdd+y.1.toAdd,
        binaryAbelianizationMap T (Additive.ofMul x.2+Additive.ofMul y.2))) = _
      rw [map_add]
      change Multiplicative.ofAdd (p
        ((x.1.toAdd,binaryAbelianizationMap T (Additive.ofMul x.2)) +
          (y.1.toAdd,binaryAbelianizationMap T (Additive.ofMul y.2)))) = _
      rw [map_add]
      rfl
    · rfl

theorem terminalRawRecordGroupMap_range (u : ℕ) (U : Submodule (ZMod 2) V)
    (hU : Module.finrank (ZMod 2) U=u)
    (f : BinaryAbelianization T →ₗ[ZMod 2] V ⧸ U)
    (p : TerminalRankRecordMaps u U f) :
    (terminalRawRecordGroupMap u p.1).range=terminalLinearQuotientGraph U f := by
  subst u
  exact terminalRecordGroupMap_range U f p

theorem terminalRawRecordGroupMap_injective (u : ℕ)
    (p : TerminalOrderedMaps (A := BinaryAbelianization T) (V := V) u) :
    Function.Injective (terminalRawRecordGroupMap u p.1) := by
  rintro ⟨b,t⟩ ⟨c,s⟩ h
  have hts : t=s := congrArg Prod.snd h
  subst s
  apply Prod.ext
  · apply Multiplicative.toAdd.injective
    apply p.2
    have hp := congrArg (fun x : Multiplicative V × T => x.1.toAdd) h
    change p.1 (b.toAdd,binaryAbelianizationMap T (Additive.ofMul t)) =
      p.1 (c.toAdd,binaryAbelianizationMap T (Additive.ofMul t)) at hp
    have hb : (b.toAdd,binaryAbelianizationMap T (Additive.ofMul t)) =
      (b.toAdd,0)+(0,binaryAbelianizationMap T (Additive.ofMul t)) := by simp
    have hc : (c.toAdd,binaryAbelianizationMap T (Additive.ofMul t)) =
      (c.toAdd,0)+(0,binaryAbelianizationMap T (Additive.ofMul t)) := by simp
    rw [hb,hc,map_add,map_add,add_right_cancel_iff] at hp
    exact hp
  · rfl

/-- Fixed-rank sum identity for any original image weight, including the
entire central-lift fibre weight. -/
theorem terminalRankRecords_weight_sum [Finite T] [Finite V] (u : ℕ)
    (w : Subgroup (Multiplicative V × T) → ℝ) :
    (∑ p : TerminalOrderedMaps (A := BinaryAbelianization T) (V := V) u,
      w (terminalRawRecordGroupMap u p.1).range) =
      (terminalRecordDivisor u (binaryCharacterRank T) : ℝ) *
        ∑ U : {U : Submodule (ZMod 2) V // Module.finrank (ZMod 2) U=u},
          ∑ f : BinaryAbelianization T →ₗ[ZMod 2] V ⧸ U.1,
            w (terminalLinearQuotientGraph U.1 f) := by
  haveI (U : Submodule (ZMod 2) V) : Finite (V ⧸ U) :=
    Finite.of_surjective U.mkQ U.mkQ_surjective
  calc
    _ = ∑ z : (Σ U : {U : Submodule (ZMod 2) V // Module.finrank (ZMod 2) U=u},
        Σ f : BinaryAbelianization T →ₗ[ZMod 2] V ⧸ U.1,
          TerminalRankRecordMaps u U.1 f),
          w (terminalRawRecordGroupMap u z.2.2.1).range :=
      (Fintype.sum_equiv (terminalRankRecordsEquiv u) _ _ (fun _ => rfl)).symm
    _ = ∑ U : {U : Submodule (ZMod 2) V // Module.finrank (ZMod 2) U=u},
        ∑ f : BinaryAbelianization T →ₗ[ZMod 2] V ⧸ U.1,
          ∑ p : TerminalRankRecordMaps u U.1 f, w (terminalLinearQuotientGraph U.1 f) := by
      simp only [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro U _
      apply Finset.sum_congr rfl
      intro f _
      apply Finset.sum_congr rfl
      intro p _
      rw [terminalRawRecordGroupMap_range u U.1 U.2 f p]
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U _
      apply Finset.sum_congr rfl
      intro f _
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Nat.card_eq_fintype_card]
      rw [terminalRankRecordMaps_card u U.1 U.2 f,binaryAbelianization_finrank]


end Groups
end SymmetricSubgroupAsymptotics
