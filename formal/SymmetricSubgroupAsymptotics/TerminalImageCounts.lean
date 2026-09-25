import SymmetricSubgroupAsymptotics.TerminalRecordFibreWeights

/-! Actual terminal subgroups and their complete original quotient images. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics
attribute [local instance] Fintype.ofFinite

local instance {D F : Type*} [AddCommGroup D] [Module (ZMod 2) D]
    [AddCommGroup F] [Module (ZMod 2) F] [Finite D] [Finite F] :
    Finite (D →ₗ[ZMod 2] F) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

variable {ι : Type} [Fintype ι] (a : ℕ) (s : ι → Bool) (T : Type) [Group T]

/-- Actual subgroups, onto the entire exterior and every original nonabelian
critical factor. Extra regular C2/V4 fullness conditions select a subfamily. -/
abbrev TerminalActualSubgroups :=
  {H : Subgroup (CriticalProductGroup a s × T) //
    H.map (MonoidHom.snd _ T)=⊤ ∧ ∀ i,
      H.map ((criticalProductFactorProjection a s i).comp (MonoidHom.fst _ T))=⊤}

/-- Fullness of the original quotient coordinates of an actual image. -/
def TerminalQuotientImageFull
    (Y : Subgroup (Multiplicative (Fin (criticalProductRank a s) → ZMod 2) × T)) : Prop :=
  ∀ i, Function.Surjective
    (fun y : Y => (criticalProductChart a s y.1.1.toAdd).2 i)

/-- The original image of an actual terminal subgroup retains the full T. -/
def terminalActualImage (H : TerminalActualSubgroups a s T) :
    TerminalFullImages (V := Fin (criticalProductRank a s) → ZMod 2) (T := T) :=
  ⟨H.1.map (terminalProductImageMap (T := T) (criticalProductQuotient a s)),by
    rw [Subgroup.map_map]
    exact H.2.1⟩

theorem terminalActualImage_full (H : TerminalActualSubgroups a s T) :
    TerminalQuotientImageFull a s T (terminalActualImage a s T H).1 := by
  intro i v
  let w := (criticalFactorChart (s i)).symm v
  let g : BinaryHeisenberg (criticalFactorHalfRank (s i)) := ⟨w.1,w.2,0⟩
  have hg : g ∈ H.1.map ((criticalProductFactorProjection a s i).comp (MonoidHom.fst _ T)) := by
    rw [H.2.2 i]
    trivial
  obtain ⟨x,hx,hg⟩ := Subgroup.mem_map.mp hg
  refine ⟨⟨terminalProductImageMap (T := T) (criticalProductQuotient a s) x,
    Subgroup.mem_map.mpr ⟨x,hx,rfl⟩⟩,?_⟩
  change (criticalProductChart a s (criticalProductQuotient a s x.1).toAdd).2 i=v
  rw [criticalProductQuotient_chart]
  change x.1.2 i=g at hg
  change (criticalFactorChart (s i)) ((x.1.2 i).a,(x.1.2 i).b)=v
  rw [hg]
  exact (criticalFactorChart (s i)).apply_symm_apply v

/-- The actual original image fibre is counted only on surviving full
quotient images. This is a cardinality definition, not a proposed estimate. -/
def terminalOriginalImageWeight [Finite T]
    (Y : Subgroup (Multiplicative (Fin (criticalProductRank a s) → ZMod 2) × T)) : ℝ :=
  if TerminalQuotientImageFull a s T Y then
    (Nat.card {H : Subgroup (CriticalProductGroup a s × T) //
      H.map (terminalProductImageMap (T := T) (criticalProductQuotient a s))=Y} : ℝ) else 0

theorem terminalOriginalImageWeight_nonneg [Finite T] (Y) :
    0 ≤ terminalOriginalImageWeight a s T Y := by
  unfold terminalOriginalImageWeight
  split_ifs <;> positivity

/-- Partition by the literal quotient image, enlarging each surviving fibre
only to all subgroups with that same entire image. -/
theorem terminalActualSubgroups_card_le_images [Finite T] :
    (Nat.card (TerminalActualSubgroups a s T) : ℝ) ≤
      ∑ Y : TerminalFullImages (V := Fin (criticalProductRank a s) → ZMod 2) (T := T),
        terminalOriginalImageWeight a s T Y.1 := by
  let f := terminalActualImage a s T
  have he : (Nat.card (TerminalActualSubgroups a s T) : ℝ) =
      ∑ Y : TerminalFullImages (V := Fin (criticalProductRank a s) → ZMod 2) (T := T),
        (Nat.card {H : TerminalActualSubgroups a s T // f H=Y} : ℝ) := by
    have hn := (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    rw [Nat.card_sigma] at hn
    exact_mod_cast hn
  rw [he]
  apply Finset.sum_le_sum
  intro Y _
  unfold terminalOriginalImageWeight
  split_ifs with hY
  · let encode : {H : TerminalActualSubgroups a s T // f H=Y} →
        {H : Subgroup (CriticalProductGroup a s × T) //
          H.map (terminalProductImageMap (T := T) (criticalProductQuotient a s))=Y.1} :=
      fun H => ⟨H.1.1,congrArg Subtype.val H.2⟩
    have hi : Function.Injective encode := by
      intro H H' h
      have hh := congrArg (fun Z : {H : Subgroup (CriticalProductGroup a s × T) //
          H.map (terminalProductImageMap (T := T) (criticalProductQuotient a s))=Y.1} => Z.1) h
      exact Subtype.ext (Subtype.ext hh)
    exact_mod_cast Nat.card_le_card_of_injective encode hi
  · haveI : IsEmpty {H : TerminalActualSubgroups a s T // f H=Y} := ⟨by
      intro H
      apply hY
      rw [← congrArg Subtype.val H.2]
      exact terminalActualImage_full a s T H.1⟩
    simp

/-- The actual image sum uses the exact original quotient-graph
classification, before rank bins or original-record divisors are introduced. -/
theorem terminalActualSubgroups_card_le_graphs [Finite T] :
    (Nat.card (TerminalActualSubgroups a s T) : ℝ) ≤
      ∑ U : Submodule (ZMod 2) (Fin (criticalProductRank a s) → ZMod 2),
        ∑ f : BinaryAbelianization T →ₗ[ZMod 2] (Fin (criticalProductRank a s) → ZMod 2) ⧸ U,
          terminalOriginalImageWeight a s T (terminalLinearQuotientGraph U f) := by
  haveI (U : Submodule (ZMod 2) (Fin (criticalProductRank a s) → ZMod 2)) :
      Finite ((Fin (criticalProductRank a s) → ZMod 2) ⧸ U) :=
    Finite.of_surjective U.mkQ U.mkQ_surjective
  refine (terminalActualSubgroups_card_le_images a s T).trans_eq ?_
  calc
    _ = ∑ p : (Σ U : Submodule (ZMod 2) (Fin (criticalProductRank a s) → ZMod 2),
        BinaryAbelianization T →ₗ[ZMod 2] (Fin (criticalProductRank a s) → ZMod 2) ⧸ U),
          terminalOriginalImageWeight a s T (terminalLinearQuotientGraph p.1 p.2) := by
      exact (Fintype.sum_equiv (terminalGraphLinearClassification
        (V := Fin (criticalProductRank a s) → ZMod 2) (T := T)).symm _ _ (fun _ => rfl)).symm
    _ = _ := by simp only [Fintype.sum_sigma]

/-- Fullness of each record's original quotient image is exactly fullness
of the physical linear coordinate maps on the complete binary domain. -/
theorem terminalRawRecord_image_full_iff [Finite T] (u : ℕ)
    (p : ((Fin u → ZMod 2) × BinaryAbelianization T) →ₗ[ZMod 2]
      (Fin (criticalProductRank a s) → ZMod 2)) :
    TerminalQuotientImageFull a s T (terminalRawRecordGroupMap u p).range ↔
      ∀ i, Function.Surjective (fun x => (terminalRecordPhysicalMap a s u T p x).2 i) := by
  constructor
  · intro h i v
    obtain ⟨y,hy⟩ := h i v
    obtain ⟨x,hx⟩ := y.2
    refine ⟨(x.1.toAdd,binaryAbelianizationMap T (Additive.ofMul x.2)),?_⟩
    change (criticalProductChart a s (p _)).2 i=v
    change (criticalProductChart a s y.1.1.toAdd).2 i=v at hy
    rw [← hx] at hy
    exact hy
  · intro h i v
    obtain ⟨⟨b,z⟩,hz⟩ := h i v
    obtain ⟨t,ht⟩ := binaryAbelianizationMap_surjective T z
    refine ⟨⟨terminalRawRecordGroupMap u p (Multiplicative.ofAdd b,t.toMul),
      ⟨(Multiplicative.ofAdd b,t.toMul),rfl⟩⟩,?_⟩
    change (criticalProductChart a s (p (b,binaryAbelianizationMap T t))).2 i=v
    rw [ht]
    exact hz

/-- Every surviving original image weight is exactly the full central
weight of its record; no comparison group or new divisor is introduced. -/
theorem terminalOriginalImageWeight_record [Finite T] (u : ℕ)
    (p : TerminalOrderedMaps (A := BinaryAbelianization T)
      (V := Fin (criticalProductRank a s) → ZMod 2) u) :
    terminalOriginalImageWeight a s T (terminalRawRecordGroupMap u p.1).range =
      if ∀ i, Function.Surjective (fun x => (terminalRecordPhysicalMap a s u T p.1 x).2 i) then
        terminalCriticalMapWeight a s u T (terminalRecordPhysicalMap a s u T p.1) else 0 := by
  unfold terminalOriginalImageWeight
  rw [terminalRawRecord_image_full_iff]
  split_ifs
  · exact terminalOriginalRecordFibre_card a s u T p
  · rfl

end SymmetricSubgroupAsymptotics

