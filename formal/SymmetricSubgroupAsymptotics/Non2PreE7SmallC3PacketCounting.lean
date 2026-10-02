import SymmetricSubgroupAsymptotics.Non2PreE7SmallC3PacketStructure
import SymmetricSubgroupAsymptotics.Non2PreE7NoPairNoC3PhysicalFrontier
import SymmetricSubgroupAsymptotics.RepeatedC3PureProfile
import SymmetricSubgroupAsymptotics.OutsideOrbitTernaryChart

/-!
# Counting the complete degree-three pre-E7 packet

The packet is split by whether the simultaneously extracted tail is empty.
Both maps below forget only witnesses and retain the literal original
permutation subgroup, so their injectivity is immediate from subgroup value.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

open RepeatedC3TailPhysical RepeatedC3TailExtraction

/-- The exact part of the no-pair/no-C3 residual for which every violating
orbit has degree three. -/
abbrev PreE7SmallC3PacketSubgroupSet (n : ℕ) :=
  {G : PreE7NoPairNoC3ResidualSubgroupSet n //
    AllPreE7ViolationOrbitsDegreeThree G.1}

abbrev PreE7SmallC3PacketPositive (n : ℕ) :=
  {G : PreE7SmallC3PacketSubgroupSet n // 0 < tailDegree G.1.1}

abbrev PreE7SmallC3PacketPure (n : ℕ) :=
  {G : PreE7SmallC3PacketSubgroupSet n // tailDegree G.1.1 = 0}

def preE7SmallC3PacketPartitionEquiv (n : ℕ) :
    PreE7SmallC3PacketSubgroupSet n ≃
      PreE7SmallC3PacketPure n ⊕ PreE7SmallC3PacketPositive n := by
  let e := (Equiv.sumCompl
    (fun G : PreE7SmallC3PacketSubgroupSet n => tailDegree G.1.1 = 0)).symm
  refine e.trans (Equiv.sumCongr (Equiv.refl _) ?_)
  exact Equiv.subtypeEquivRight (fun G => by omega)

/-- Finite positive-tail profile parameters at ambient degree `n`. -/
structure RepeatedC3PositiveProfileIndex (n : ℕ) where
  c : Fin (n + 1)
  m : Fin (n + 1)
  c_pos : 0 < c
  m_pos : 0 < m
  degree_eq : 3 * c + m = n
  deriving Fintype

/-- Finite pure-profile parameters at ambient degree `n`. -/
structure RepeatedC3PureProfileIndex (n : ℕ) where
  c : Fin (n + 1)
  c_pos : 0 < c
  degree_eq : 3 * c = n
  deriving Fintype

private theorem packet_has_regularOrbit {n : ℕ}
    (G : PreE7SmallC3PacketSubgroupSet n) :
    ∃ o : OrbitProfileFromOrbits.Orbit G.1.1,
      IsRegularC3Orbit G.1.1 o := by
  obtain ⟨o, hbad⟩ := exists_preE7ViolationOrbit G.1.1 G.1.2.1.1.2
  let outside : RepeatedMarkerOwnerBound.OutsideOrbit G.1.1 :=
    ⟨o, hbad.1, hbad.2.1⟩
  have hcard : Nat.card o.orbit = 3 := G.2 o hbad
  obtain ⟨e, he⟩ :=
    RepeatedMarkerOwnerBound.outsideOrbit_degree_three_ternary_chart
      G.1.1 outside hcard
  have hp0 : IsPGroup 3 ternaryRegularAction :=
    IsPGroup.iff_card.mpr ⟨1, by
      rw [ternaryRegularAction_card]
      norm_num⟩
  let g : ternaryRegularAction ≃*
      OrbitProfileFromOrbits.orbitImage G.1.1 o :=
    (e.permCongrHom.subgroupMap ternaryRegularAction).trans
      (MulEquiv.subgroupCongr he)
  exact ⟨o, hcard, hp0.of_equiv g⟩

private theorem packet_regularCount_pos {n : ℕ}
    (G : PreE7SmallC3PacketSubgroupSet n) :
    0 < regularCount G.1.1 := by
  obtain ⟨o, ho⟩ := packet_has_regularOrbit G
  exact regularCount_pos G.1.1 o ho

private theorem packet_degree_eq {n : ℕ}
    (G : PreE7SmallC3PacketSubgroupSet n) :
    3 * regularCount G.1.1 + tailDegree G.1.1 = n := by
  simpa only [Fintype.card_fin] using degree_eq G.1.1

private def positiveProfileIndex {n : ℕ}
    (G : PreE7SmallC3PacketPositive n) :
    RepeatedC3PositiveProfileIndex n where
  c := ⟨regularCount G.1.1.1, by
    have h := packet_degree_eq G.1
    omega⟩
  m := ⟨tailDegree G.1.1.1, by
    have h := packet_degree_eq G.1
    omega⟩
  c_pos := packet_regularCount_pos G.1
  m_pos := G.2
  degree_eq := packet_degree_eq G.1

private def pureProfileIndex {n : ℕ}
    (G : PreE7SmallC3PacketPure n) :
    RepeatedC3PureProfileIndex n where
  c := ⟨regularCount G.1.1.1, by
    have h := packet_degree_eq G.1
    omega⟩
  c_pos := packet_regularCount_pos G.1
  degree_eq := by
    have h := packet_degree_eq G.1
    rw [G.2] at h
    omega

/-- Every positive-tail packet member enters its simultaneous retained-tail
profile with the sharp `3/20` cap. -/
def positivePresentation
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    {n : ℕ} (G : PreE7SmallC3PacketPositive n) :
    Σ p : RepeatedC3PositiveProfileIndex n,
      AssembledOrbitProfileOn
        (RepeatedC3TailProfile.modelPredicate p.c
          (3 * p.m / 20) p.m) (Fin n) :=
  ⟨positiveProfileIndex G,
    repeatedC3Tail_packetAssembly hChief hWeight hPrimitive h18
      G.1.1.1 G.1.2⟩

theorem positivePresentation_injective
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    {n : ℕ} :
    Function.Injective
      (positivePresentation hChief hWeight hPrimitive h18
        (n := n)) := by
  intro G K h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z => z.2.1) h

/-- Every zero-tail packet member enters the honest one-colour pure profile. -/
def purePresentation {n : ℕ} (G : PreE7SmallC3PacketPure n) :
    Σ p : RepeatedC3PureProfileIndex n,
      AssembledOrbitProfileOn
        (RepeatedC3PureProfile.modelPredicate p.c) (Fin n) :=
  ⟨pureProfileIndex G,
    RepeatedC3PureProfile.assembled_of_tailDegree_zero G.1.1.1 G.2⟩

theorem purePresentation_injective {n : ℕ} :
    Function.Injective (purePresentation (n := n)) := by
  intro G K h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z => z.2.1) h

theorem preE7SmallC3PacketPositive_card_le
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (n : ℕ) :
    Nat.card (PreE7SmallC3PacketPositive n) ≤
      ∑ p : RepeatedC3PositiveProfileIndex n,
        Nat.card (AssembledOrbitProfileOn
          (RepeatedC3TailProfile.modelPredicate p.c
            (3 * p.m / 20) p.m) (Fin n)) := by
  letI : ∀ p : RepeatedC3PositiveProfileIndex n,
      Finite (AssembledOrbitProfileOn
        (RepeatedC3TailProfile.modelPredicate p.c
          (3 * p.m / 20) p.m) (Fin n)) := fun _ => by
    unfold AssembledOrbitProfileOn
    infer_instance
  calc
    _ ≤ Nat.card (Σ p : RepeatedC3PositiveProfileIndex n,
        AssembledOrbitProfileOn
          (RepeatedC3TailProfile.modelPredicate p.c
            (3 * p.m / 20) p.m) (Fin n)) :=
      Nat.card_le_card_of_injective
        (positivePresentation hChief hWeight hPrimitive h18)
        (positivePresentation_injective hChief hWeight hPrimitive h18)
    _ = _ := Nat.card_sigma

theorem preE7SmallC3PacketPure_card_le (n : ℕ) :
    Nat.card (PreE7SmallC3PacketPure n) ≤
      ∑ p : RepeatedC3PureProfileIndex n,
        Nat.card (AssembledOrbitProfileOn
          (RepeatedC3PureProfile.modelPredicate p.c) (Fin n)) := by
  letI : ∀ p : RepeatedC3PureProfileIndex n,
      Finite (AssembledOrbitProfileOn
        (RepeatedC3PureProfile.modelPredicate p.c) (Fin n)) := fun _ => by
    unfold AssembledOrbitProfileOn
    infer_instance
  calc
    _ ≤ Nat.card (Σ p : RepeatedC3PureProfileIndex n,
        AssembledOrbitProfileOn
          (RepeatedC3PureProfile.modelPredicate p.c) (Fin n)) :=
      Nat.card_le_card_of_injective purePresentation purePresentation_injective
    _ = _ := Nat.card_sigma

theorem preE7SmallC3Packet_card_eq (n : ℕ) :
    Nat.card (PreE7SmallC3PacketSubgroupSet n) =
      Nat.card (PreE7SmallC3PacketPure n) +
        Nat.card (PreE7SmallC3PacketPositive n) := by
  rw [Nat.card_congr (preE7SmallC3PacketPartitionEquiv n), Nat.card_sum]

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
