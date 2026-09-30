import SymmetricSubgroupAsymptotics.BinaryCarrierCanonicalOrbitPhysicalEncoding
import SymmetricSubgroupAsymptotics.FusionOrbitProfileChart

/-!
# A canonical product axis is the selected physical Goursat axis

The simultaneous canonical orbit chart and an orbit/complement chart encode
the same pointwise permutation when only one orbit coordinate moves.  This
identifies the corresponding literal carrier axis with the Goursat axis of
the complete selected-orbit deleted model.

The argument is chart-theoretic.  It does not use a classification of the
local action or an assumption on the complementary action.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierCanonicalOrbitAxisBridge

open SymmetricSubgroupAsymptotics
open BinaryCarrierCanonicalOrbitPhysicalEncoding
open BinaryCarrierRoutedProfileAxisClosure

variable {ι X Z : Type} [Fintype ι] [DecidableEq ι]
    [Fintype X] [Fintype Z]
  (Ω : ι → Type) [∀ i, Fintype (Ω i)]
  (U : ∀ i, Subgroup (Equiv.Perm (Ω i)))
  (H : Subgroup (Equiv.Perm X))
  (C : OrbitProfileFromOrbits.Data H U)

/-- The independent product permutation which moves only `q`, by `u`. -/
def canonicalSingle (q : Σ i, Fin (C.multiplicity i)) (u : U q.1) :
    Equiv.Perm (OrbitProfilePoints Ω C.multiplicity) :=
  orbitProfileProductAction C.multiplicity U
    ((flatten Ω U C.multiplicity).symm
      (MonoidHom.mulSingle
        (fun r : (Σ i, Fin (C.multiplicity i)) => U r.1) q u))

@[simp] theorem canonicalSingle_apply_same
    (q : Σ i, Fin (C.multiplicity i)) (u : U q.1) (x : Ω q.1) :
    canonicalSingle Ω U H C q u ⟨q.1,q.2,x⟩ =
      ⟨q.1,q.2,(u : Equiv.Perm (Ω q.1)) x⟩ := by
  rcases q with ⟨i,j⟩
  simp [canonicalSingle, flatten, BinaryCarrierProfileTransport.profileCurry,
    orbitProfileProductAction, orbitProfileProductPermutation]
  simp [Sigma.curry, Pi.mulSingle_eq_same]

@[simp] theorem canonicalSingle_apply_of_ne
    (q r : Σ i, Fin (C.multiplicity i))
    (u : U q.1) (h : r ≠ q) (x : Ω r.1) :
    canonicalSingle Ω U H C q u ⟨r.1,r.2,x⟩ = ⟨r.1,r.2,x⟩ := by
  rcases q with ⟨i,j⟩
  rcases r with ⟨g,k⟩
  simp [canonicalSingle, flatten, BinaryCarrierProfileTransport.profileCurry,
    orbitProfileProductAction, orbitProfileProductPermutation]
  simp [Sigma.curry, Pi.mulSingle_eq_of_ne h]

/-- The chart which separates one prescribed literal orbit from its entire
set complement. -/
def selectedChart (q : Σ i, Fin (C.multiplicity i))
    (eC : Z ≃ ↥((FusionOrbitProfileChart.orbitSubaction
      H (C.orbitIndex q))ᶜ)) : Ω q.1 ⊕ Z ≃ X :=
  FusionOrbitProfileChart.chart H (C.orbitIndex q)
    (C.localChart q.1 q.2) eC

/-- The original permutation obtained from the one-coordinate canonical
product element. -/
def canonicalSingleConjugate
    (q : Σ i, Fin (C.multiplicity i)) (u : U q.1) :
    Equiv.Perm X :=
  C.chart.permCongr (canonicalSingle Ω U H C q u)

/-- The same original permutation, now written in the selected
orbit/complement chart. -/
def selectedSingleConjugate (q : Σ i, Fin (C.multiplicity i))
    (eC : Z ≃ ↥((FusionOrbitProfileChart.orbitSubaction
      H (C.orbitIndex q))ᶜ)) (u : U q.1) : Equiv.Perm X :=
  (selectedChart Ω U H C q eC).permCongr
    (fusionOrbitAction (U q.1) (u,1))

/-- A one-coordinate move in the complete canonical chart is literally the
same permutation as that move with the entire complement fixed in the
selected orbit chart. -/
theorem canonicalSingleConjugate_eq_selectedSingleConjugate
    (q : Σ i, Fin (C.multiplicity i))
    (eC : Z ≃ ↥((FusionOrbitProfileChart.orbitSubaction
      H (C.orbitIndex q))ᶜ)) (u : U q.1) :
    canonicalSingleConjugate Ω U H C q u =
      selectedSingleConjugate Ω U H C q eC u := by
  apply Equiv.ext
  intro a
  obtain ⟨z,rfl⟩ := C.chart.surjective a
  rcases z with ⟨g,k,x⟩
  simp only [canonicalSingleConjugate, selectedSingleConjugate,
    Equiv.permCongr_apply, Equiv.symm_apply_apply]
  by_cases hq : (⟨g,k⟩ : Σ i, Fin (C.multiplicity i)) = q
  · subst q
    change C.chart (canonicalSingle Ω U H C ⟨g,k⟩ u ⟨g,k,x⟩) =
      selectedChart Ω U H C ⟨g,k⟩ eC
        (fusionOrbitAction (U g) (u,1)
          ((selectedChart Ω U H C ⟨g,k⟩ eC).symm
            (C.chart ⟨g,k,x⟩)))
    rw [canonicalSingle_apply_same Ω U H C]
    have hchart :
        C.chart ⟨g,k,x⟩ =
          selectedChart Ω U H C ⟨g,k⟩ eC (Sum.inl x) := by
      rfl
    rw [hchart, Equiv.symm_apply_apply]
    rfl
  · have hother :
        C.chart ⟨g,k,x⟩ ∈
          (C.orbitIndex (⟨g,k⟩ : Σ i, Fin (C.multiplicity i))).orbit := by
      change (C.localChart g k x : X) ∈
        (C.orbitIndex (⟨g,k⟩ : Σ i, Fin (C.multiplicity i))).orbit
      exact (C.localChart g k x).property
    have hout : C.chart ⟨g,k,x⟩ ∉ (C.orbitIndex q).orbit := by
      intro hselected
      have ho : Quotient.mk'' (C.chart ⟨g,k,x⟩) =
          C.orbitIndex (⟨g,k⟩ : Σ i, Fin (C.multiplicity i)) :=
        MulAction.orbitRel.Quotient.mem_orbit.mp hother
      have hs : Quotient.mk'' (C.chart ⟨g,k,x⟩) = C.orbitIndex q :=
        MulAction.orbitRel.Quotient.mem_orbit.mp hselected
      exact hq (C.orbitIndex.injective (ho.symm.trans hs))
    let y : ↥((FusionOrbitProfileChart.orbitSubaction
        H (C.orbitIndex q))ᶜ) := ⟨C.chart ⟨g,k,x⟩,hout⟩
    have hchart :
        selectedChart Ω U H C q eC (Sum.inr (eC.symm y)) =
          C.chart ⟨g,k,x⟩ := by
      change ((eC (eC.symm y) :
        ↥((FusionOrbitProfileChart.orbitSubaction
          H (C.orbitIndex q))ᶜ)) : X) = C.chart ⟨g,k,x⟩
      rw [Equiv.apply_symm_apply]
    change C.chart (canonicalSingle Ω U H C q u ⟨g,k,x⟩) =
      selectedChart Ω U H C q eC
        (fusionOrbitAction (U q.1) (u,1)
          ((selectedChart Ω U H C q eC).symm
            (C.chart ⟨g,k,x⟩)))
    rw [canonicalSingle_apply_of_ne Ω U H C q
      (⟨g,k⟩ : Σ i, Fin (C.multiplicity i)) u hq]
    rw [← hchart, Equiv.symm_apply_apply]
    rfl

/-- Membership in the canonical carrier axis is membership of the associated
one-orbit permutation in the original subgroup. -/
theorem mem_canonicalAxis_iff
    (q : Σ i, Fin (C.multiplicity i)) (u : U q.1) :
    u ∈ CanonicalOrbitWord.axis Ω U H C q ↔
      canonicalSingleConjugate Ω U H C q u ∈ H := by
  change MonoidHom.mulSingle
    (fun r : (Σ i, Fin (C.multiplicity i)) => U r.1) q u ∈
      (CanonicalOrbitWord.profileSource Ω U H C).map
        (flatten Ω U C.multiplicity).toMonoidHom ↔ _
  constructor
  · intro hu
    obtain ⟨d,hd,he⟩ := Subgroup.mem_map.mp hu
    have hd_eq : d = (flatten Ω U C.multiplicity).symm
        (MonoidHom.mulSingle
          (fun r : (Σ i, Fin (C.multiplicity i)) => U r.1) q u) := by
      change (flatten Ω U C.multiplicity) d =
        (MonoidHom.mulSingle
          (fun r : (Σ i, Fin (C.multiplicity i)) => U r.1) q u) at he
      apply (flatten Ω U C.multiplicity).injective
      rw [he, (flatten Ω U C.multiplicity).apply_symm_apply]
    subst d
    change canonicalSingle Ω U H C q u ∈
      CanonicalOrbitWord.model Ω U H C at hd
    have hh := (mem_relabelSubgroup C.chart.symm H
      (canonicalSingle Ω U H C q u)).mp hd
    simpa [canonicalSingleConjugate] using hh
  · intro hu
    refine Subgroup.mem_map.mpr
      ⟨(flatten Ω U C.multiplicity).symm
          (MonoidHom.mulSingle
            (fun r : (Σ i, Fin (C.multiplicity i)) => U r.1) q u), ?_,
        (flatten Ω U C.multiplicity).apply_symm_apply _⟩
    change canonicalSingle Ω U H C q u ∈
      CanonicalOrbitWord.model Ω U H C
    apply (mem_relabelSubgroup C.chart.symm H
      (canonicalSingle Ω U H C q u)).mpr
    simpa [canonicalSingleConjugate] using hu

/-- Membership in the physical Goursat axis is the same original-subgroup
membership, written in the selected orbit/complement chart. -/
theorem mem_fusionDeletedAxis_iff
    (q : Σ i, Fin (C.multiplicity i))
    (eC : Z ≃ ↥((FusionOrbitProfileChart.orbitSubaction
      H (C.orbitIndex q))ᶜ)) (u : U q.1) :
    u ∈ (fusionDeletedModel (U q.1)
      (relabelSubgroup (selectedChart Ω U H C q eC).symm H)).goursatFst ↔
        selectedSingleConjugate Ω U H C q eC u ∈ H := by
  rw [Subgroup.mem_goursatFst]
  change fusionOrbitAction (U q.1) (u,1) ∈
      relabelSubgroup (selectedChart Ω U H C q eC).symm H ↔ _
  rw [mem_relabelSubgroup]
  simp only [Equiv.symm_symm]
  rfl

/-- The literal coordinate axis of the complete canonical orbit word is the
Goursat axis of the same original subgroup in any complete chart separating
that orbit from its full set complement. -/
theorem canonicalAxis_eq_fusionDeletedAxis
    (q : Σ i, Fin (C.multiplicity i))
    (eC : Z ≃ ↥((FusionOrbitProfileChart.orbitSubaction
      H (C.orbitIndex q))ᶜ)) :
    CanonicalOrbitWord.axis Ω U H C q =
      (fusionDeletedModel (U q.1)
        (relabelSubgroup (selectedChart Ω U H C q eC).symm H)).goursatFst := by
  ext u
  rw [mem_canonicalAxis_iff Ω U H C q u,
    mem_fusionDeletedAxis_iff Ω U H C q eC u,
    canonicalSingleConjugate_eq_selectedSingleConjugate Ω U H C q eC u]

end SymmetricSubgroupAsymptotics.BinaryCarrierCanonicalOrbitAxisBridge

end
