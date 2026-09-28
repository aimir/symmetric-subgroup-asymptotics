import SymmetricSubgroupAsymptotics.C1DegreeNineRankBudget
import SymmetricSubgroupAsymptotics.FusionComplementOrbits
import SymmetricSubgroupAsymptotics.TernaryHighOwnerCapacity

/-!
# The one-C3 source pattern survives deletion of a nonmarker orbit

Deleting one literal orbit whose action is not the regular degree-three
`C3` action preserves the unique regular `C3` orbit and the absence of a
natural `A4` orbit.  The proof uses the exact complement-image orbit
transport, so every induced action is retained on its original point set up
to the displayed chart.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

open FusionOrbitProfileChart

/-- The retained one-regular-`C3`, no-natural-`A4` pattern survives deletion
of any selected orbit which is not itself regular `C3`. -/
theorem C1DegreeNineSourcePattern.complementImage
    {X Z : Type} [Fintype X] [Fintype Z]
    (H : Subgroup (Equiv.Perm X))
    (selected : OrbitProfileFromOrbits.Orbit H)
    (eC : Z ≃ ↥((orbitSubaction H selected)ᶜ))
    (hpattern : C1DegreeNineSourcePattern H)
    (hselected : ¬ IsRegularC3Orbit H selected) :
    C1DegreeNineSourcePattern
      (Complement.image H selected eC) := by
  obtain ⟨ambientExceptional, hregular, hunique, hnoA4⟩ := hpattern
  have hne : selected ≠ ambientExceptional := by
    intro h
    apply hselected
    rwa [h]
  have hout : ambientExceptional.out ∉ selected.orbit := by
    intro hmem
    have hq : Quotient.mk'' ambientExceptional.out = selected :=
      (MulAction.orbitRel.Quotient.mem_orbit).mp hmem
    apply hne
    exact hq.symm.trans (Quotient.out_eq' ambientExceptional)
  let exceptionalPoint : Z :=
    eC.symm ⟨ambientExceptional.out, hout⟩
  let exceptional : OrbitProfileFromOrbits.Orbit
      (Complement.image H selected eC) := Quotient.mk'' exceptionalPoint
  have hambientExceptional :
      Complement.ambientOrbit H selected eC exceptional =
        ambientExceptional := by
    have hp : exceptionalPoint ∈ exceptional.orbit := by
      change exceptionalPoint ∈
        MulAction.orbitRel.Quotient.orbit
          (Quotient.mk'' exceptionalPoint :
          OrbitProfileFromOrbits.Orbit
            (Complement.image H selected eC))
      rw [MulAction.orbitRel.Quotient.orbit_mk]
      exact MulAction.mem_orbit_self exceptionalPoint
    have himage :
        ((eC exceptionalPoint : ↥((orbitSubaction H selected)ᶜ)) : X) ∈
          (Complement.ambientOrbit H selected eC exceptional).orbit :=
      (Complement.orbitEquiv H selected eC exceptional
        ⟨exceptionalPoint, hp⟩).property
    have hq : Quotient.mk''
        ((eC exceptionalPoint : ↥((orbitSubaction H selected)ᶜ)) : X) =
          Complement.ambientOrbit H selected eC exceptional :=
      (MulAction.orbitRel.Quotient.mem_orbit).mp himage
    refine hq.symm.trans ?_
    simp only [exceptionalPoint, Equiv.apply_symm_apply]
    exact Quotient.out_eq' ambientExceptional
  have transferPGroup
      (o : OrbitProfileFromOrbits.Orbit
        (Complement.image H selected eC))
      (h : IsPGroup 3
        (OrbitProfileFromOrbits.orbitImage H
          (Complement.ambientOrbit H selected eC o))) :
      IsPGroup 3
        (OrbitProfileFromOrbits.orbitImage
          (Complement.image H selected eC) o) := by
    let e := Complement.orbitEquiv H selected eC o
    let g : OrbitProfileFromOrbits.orbitImage
          (Complement.image H selected eC) o ≃*
        OrbitProfileFromOrbits.orbitImage H
          (Complement.ambientOrbit H selected eC o) :=
      (e.permCongrHom.subgroupMap
        (OrbitProfileFromOrbits.orbitImage
          (Complement.image H selected eC) o)).trans
        (MulEquiv.subgroupCongr
          (Complement.relabel_orbitImage H selected eC o))
    exact h.of_equiv g.symm
  have hregularExceptional : IsRegularC3Orbit
      (Complement.image H selected eC) exceptional := by
    constructor
    · calc
        Nat.card exceptional.orbit =
            Nat.card (Complement.ambientOrbit H selected eC exceptional).orbit :=
          Nat.card_congr (Complement.orbitEquiv H selected eC exceptional)
        _ = Nat.card ambientExceptional.orbit := by rw [hambientExceptional]
        _ = 3 := hregular.1
    · apply transferPGroup exceptional
      rw [hambientExceptional]
      exact hregular.2
  refine ⟨exceptional, hregularExceptional, ?_, ?_⟩
  · intro o ho
    have hambientRegular : IsRegularC3Orbit H
        (Complement.ambientOrbit H selected eC o) := by
      constructor
      · calc
          Nat.card (Complement.ambientOrbit H selected eC o).orbit =
              Nat.card o.orbit :=
            (Nat.card_congr (Complement.orbitEquiv H selected eC o)).symm
          _ = 3 := ho.1
      · let e := Complement.orbitEquiv H selected eC o
        let g : OrbitProfileFromOrbits.orbitImage
              (Complement.image H selected eC) o ≃*
            OrbitProfileFromOrbits.orbitImage H
              (Complement.ambientOrbit H selected eC o) :=
          (e.permCongrHom.subgroupMap
            (OrbitProfileFromOrbits.orbitImage
              (Complement.image H selected eC) o)).trans
            (MulEquiv.subgroupCongr
              (Complement.relabel_orbitImage H selected eC o))
        exact ho.2.of_equiv g
    have heq := hunique (Complement.ambientOrbit H selected eC o)
      hambientRegular
    apply Complement.ambientOrbit_injective H selected eC
    rw [heq, hambientExceptional]
  · intro o hA4
    have htransport := TernaryHighEarlierOwner.naturalA4_relabel
      (Complement.orbitEquiv H selected eC o)
      (OrbitProfileFromOrbits.orbitImage
        (Complement.image H selected eC) o) hA4
    rw [Complement.relabel_orbitImage H selected eC o] at htransport
    exact hnoA4 (Complement.ambientOrbit H selected eC o) htransport

/-- The numerical rank budget is the smaller invariant consequence needed
by the degree-nine ternary epimorphism row. -/
theorem C1DegreeNineSourcePattern.complementImage_rankBudget
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    {X : Type} [Fintype X] {c : ℕ}
    (H : Subgroup (Equiv.Perm X))
    (selected : OrbitProfileFromOrbits.Orbit H)
    (eC : Fin c ≃ ↥((orbitSubaction H selected)ᶜ))
    (hpattern : C1DegreeNineSourcePattern H)
    (hselected : ¬ IsRegularC3Orbit H selected) :
    C1DegreeNineRankBudget (Complement.image H selected eC) :=
  (hpattern.complementImage H selected eC hselected).rankBudget
    hChief hPrimitive h18 (Complement.image H selected eC)

/-- In an exact selected-orbit chart, deleting a nonmarker orbit attaches the
degree-nine rank budget to the literal source projection of the actual fusion
model. -/
theorem C1DegreeNineSourcePattern.deletedModel_rankBudget
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    {X : Type} [Fintype X] {w c : ℕ}
    (H : Subgroup (Equiv.Perm X))
    (selected : OrbitProfileFromOrbits.Orbit H)
    (U : Subgroup (Equiv.Perm (Fin w)))
    (eO : Fin w ≃ selected.orbit)
    (eC : Fin c ≃ ↥((orbitSubaction H selected)ᶜ))
    (himage : relabelSubgroup eO U =
      OrbitProfileFromOrbits.orbitImage H selected)
    (hpattern : C1DegreeNineSourcePattern H)
    (hselected : ¬ IsRegularC3Orbit H selected) :
    C1DegreeNineRankBudget
      ((fusionDeletedModel U
          (relabelSubgroup (chart H selected eO eC).symm H)).map
        (MonoidHom.snd U (Equiv.Perm (Fin c)))) := by
  rw [Complement.deletedSource_eq_image H selected eO eC U himage]
  exact hpattern.complementImage_rankBudget hChief hPrimitive h18
    H selected eC hselected

end SymmetricSubgroupAsymptotics

end
