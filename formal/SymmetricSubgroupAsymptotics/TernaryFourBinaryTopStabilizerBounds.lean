import SymmetricSubgroupAsymptotics.SignedMonomialFixedTopCode
import SymmetricSubgroupAsymptotics.SignedMonomialLargeKernelSupportIndex
import SymmetricSubgroupAsymptotics.TransitiveUniqueCoordinateSubgroupIndex
import SymmetricSubgroupAsymptotics.TernaryFourSignedStabilizerCapacity

/-! Actual vector stabilizers for transitive signed four-coordinate
groups with projected top of order at most eight. Unique supports retain
the full coordinate index. A large sign kernel supplies the additional
pair-support index, without classifying support orbits or binary tops. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics.TernaryFourBinaryTopStabilizerBounds
open TernarySignedWreathLinearEquiv TernaryFourProperModuleSignKernel
open SignedMonomialFixedCoordinateCode SignedMonomialStabilizerClassBound
open SignedMonomialFixedTopCode

private theorem units_card : Nat.card (ZMod 3)ˣ=2 :=
  (Nat.card_congr OddMarkerTernaryChart.signScalarEquiv.symm.toEquiv).trans
    ((Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2)).trans
      (Nat.card_zmod 2))

private theorem top_support_preserves (R : Subgroup Signed) (v : Fin 4 → ZMod 3)
    (q : (topHom R).range) (hq : q∈supportTopStabilizer (topHom R) v) (i : Fin 4) :
    v (q.val i)≠0 ↔ v i≠0 := by
  let S : Set (Fin 4) := {i : Fin 4 | v i≠0}
  have hfix : q.val • S=S := hq
  have h : q.val • i∈q.val • S ↔ i∈S := Set.smul_mem_smul_set_iff
  rw [hfix] at h
  exact h

theorem unique_support_bounds (R : Subgroup Signed)
    (htrans : ∀ i j : Fin 4,∃g : R,topHom R g i=j)
    (hQ : Nat.card (topHom R).range≤8) (v : Fin 4 → ZMod 3)
    (hunique : Nat.card {i : Fin 4 // v i≠0}=1 ∨ Nat.card {i : Fin 4 // v i=0}=1) :
    4*Nat.card (fixedSubgroup ((linearHom (Fin 4)).comp R.subtype) v)≤Nat.card R ∧
      Nat.card (ConjClasses (fixedSubgroup ((linearHom (Fin 4)).comp R.subtype) v))≤
        2^Nat.card {i : Fin 4 // v i=0}*2 := by
  let ρ := (linearHom (Fin 4)).comp R.subtype
  let t := topHom R
  change Nat.card t.range≤8 at hQ
  let a : R → Fin 4 → (ZMod 3)ˣ := fun g i => coefficient (Fin 4) g.val i
  let U := fixedSubgroup ρ v
  let C := supportTopStabilizer t v
  have htransQ : ∀ i j : Fin 4,∃q : t.range,q.val i=j := by
    intro i j
    obtain ⟨g,hg⟩ := htrans i j
    exact ⟨⟨t g,⟨g,rfl⟩⟩,hg⟩
  have bound (P : Fin 4 → Prop) (hcard : Nat.card {i : Fin 4 // P i}=1)
      (hvP : ∀ (g : R),g∈U → ∀ i,P (t g i) ↔ P i)
      (hqP : ∀ (q : t.range),q∈C → ∀ i,P (q.val i) ↔ P i) :
      4*Nat.card U≤Nat.card R ∧ Nat.card C≤2 := by
    have hU := TransitiveUniqueCoordinateSubgroupIndex.degree_mul_card_le t htrans U P hcard hvP
    have hC := TransitiveUniqueCoordinateSubgroupIndex.degree_mul_card_le
      t.range.subtype htransQ C P hcard hqP
    rw [Nat.card_fin] at hU hC
    exact ⟨hU,by omega⟩
  have hperm (g : R) (hg : g∈U) (i : Fin 4) : v (t g i)≠0 ↔ v i≠0 :=
    fixed_support_iff ρ t a (fun g w i => linearHom_apply (Fin 4) g.val w i) g v hg i
  have hb : 4*Nat.card U≤Nat.card R ∧ Nat.card C≤2 := by
    rcases hunique with hs|hz
    · exact bound (fun i => v i≠0) hs hperm (top_support_preserves R v)
    · exact bound (fun i => v i=0) hz
        (fun g hg i => by simpa only [not_not] using not_congr (hperm g hg i))
        (fun q hq i => by simpa only [not_not] using not_congr (top_support_preserves R v q hq i))
  refine ⟨hb.1,?_⟩
  have hc := fixed_card_le_zero_units_mul_top_stabilizer ρ t a
    (fun g w i => linearHom_apply (Fin 4) g.val w i)
    ((linearHom_injective (Fin 4)).comp Subtype.val_injective) v
  rw [units_card] at hc
  calc
    _≤Nat.card U := Nat.card_le_card_of_surjective (@ConjClasses.mk U _) ConjClasses.mk_surjective
    _≤2^Nat.card {i : Fin 4 // v i=0}*Nat.card C := hc
    _≤2^Nat.card {i : Fin 4 // v i=0}*2 := Nat.mul_le_mul_left _ hb.2

theorem proper_support_index (R : Subgroup Signed)
    (htrans : ∀ i j : Fin 4,∃g : R,topHom R g i=j) (v : Fin 4 → ZMod 3)
    (hS : {i : Fin 4 | v i≠0}.Nonempty) (hZ : {i : Fin 4 | v i=0}.Nonempty) :
    2*Nat.card (fixedSubgroup ((linearHom (Fin 4)).comp R.subtype) v)≤Nat.card R := by
  let ρ := (linearHom (Fin 4)).comp R.subtype
  let t := topHom R
  letI : MulAction R (Fin 4) := MulAction.compHom _ t
  let S : Set (Fin 4) := {i : Fin 4 | v i≠0}
  let B := MulAction.stabilizer R S
  have hB : B≠⊤ := TransitiveSetStabilizerIndexBounds.set_stabilizer_ne_top htrans S hS (by
    obtain ⟨i,hi⟩ := hZ
    exact ⟨i,fun hn => hn hi⟩)
  have hle : fixedSubgroup ρ v≤B := by
    intro g hg
    change t g • S=S
    apply Set.ext
    intro i
    simp only [Set.mem_smul_set_iff_inv_smul_mem]
    change v ((t g).symm i)≠0 ↔ v i≠0
    have h := fixed_support_iff ρ t (fun g i => coefficient (Fin 4) g.val i)
      (fun g w i => linearHom_apply (Fin 4) g.val w i) g v hg ((t g).symm i)
    simpa only [Equiv.apply_symm_apply] using h.symm
  have hidx : 2≤(fixedSubgroup ρ v).index :=
    (show 2≤B.index from B.one_lt_index_of_ne_top hB).trans (Subgroup.index_antitone hle)
  calc
    _≤(fixedSubgroup ρ v).index*Nat.card (fixedSubgroup ρ v) := Nat.mul_le_mul_right _ hidx
    _=Nat.card R := (fixedSubgroup ρ v).index_mul_card

theorem large_kernel_pair_support_index (R : Subgroup Signed)
    (htrans : ∀ i j : Fin 4,∃g : R,topHom R g i=j) (v : Fin 4 → ZMod 3)
    (hS : {i : Fin 4 | v i≠0}.Nonempty) (hZ : {i : Fin 4 | v i=0}.Nonempty)
    (hz : Nat.card {i : Fin 4 // v i=0}=2) (hlarge : 4<Nat.card (topHom R).ker) :
    4*Nat.card (fixedSubgroup ((linearHom (Fin 4)).comp R.subtype) v)≤Nat.card R := by
  apply SignedMonomialLargeKernelSupportIndex.four_mul_fixed_card_le_of_large_kernel
    ((linearHom (Fin 4)).comp R.subtype) (topHom R)
    (fun g i => coefficient (Fin 4) g.val i)
    (fun g w i => linearHom_apply (Fin 4) g.val w i)
    ((linearHom_injective (Fin 4)).comp Subtype.val_injective) htrans v hS hZ
  simpa only [units_card,hz] using hlarge

end SymmetricSubgroupAsymptotics.TernaryFourBinaryTopStabilizerBounds
