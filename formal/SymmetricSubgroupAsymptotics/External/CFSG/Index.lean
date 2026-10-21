import SymmetricSubgroupAsymptotics.External.CFSG.Models.LieFamilies
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Sporadic
import Mathlib.GroupTheory.SpecificGroups.Alternating

namespace CFSG

/-- An explicit, deliberately non-disjoint list of the CFSG models.
Rank is root-system rank; `q.order` is the untwisted field parameter.
The twisted A/D/E6 models use GF(q²), triality uses GF(q³).
Exceptional isomorphisms are allowed to duplicate entries. -/
inductive Index
  | cyclic (p : ℕ) (prime : p.Prime)
  | alternating (n : ℕ) (degree : 5 ≤ n)
  | A (r : ℕ) (q : PrimePower) (rank : 1 ≤ r)
      (small : r = 1 → 4 ≤ q.order)
  | B (r : ℕ) (q : PrimePower) (rank : 3 ≤ r)
  | C (r : ℕ) (q : PrimePower) (rank : 2 ≤ r)
      (small : r = 2 → q.order ≠ 2)
  | D (r : ℕ) (q : PrimePower) (rank : 4 ≤ r)
  | E6 (q : PrimePower)
  | E7 (q : PrimePower)
  | E8 (q : PrimePower)
  | F4 (q : PrimePower)
  | G2 (q : PrimePower) (small : q.order ≠ 2)
  | twistedA (r : ℕ) (q : PrimePower) (rank : 2 ≤ r)
      (small : r = 2 → q.order ≠ 2)
  | twistedD (r : ℕ) (q : PrimePower) (rank : 4 ≤ r)
  | twistedE6 (q : PrimePower)
  | trialityD4 (q : PrimePower)
  | suzuki (m : ℕ) (positive : 1 ≤ m)
  | reeG2 (m : ℕ) (positive : 1 ≤ m)
  | reeF4 (m : ℕ) (positive : 1 ≤ m)
  | tits
  | sporadic (s : Sporadic)

namespace Index
noncomputable section

def Model : Index → Type
  | .cyclic p _ => Multiplicative (ZMod p)
  | .alternating n _ => ↥(alternatingGroup (Fin n))
  | .A r q _ _ => Models.A r q
  | .B r q _ => Models.B r q
  | .C r q _ _ => Models.C r q
  | .D r q _ => Models.D r q
  | .E6 q => Models.E6 q
  | .E7 q => Models.E7 q
  | .E8 q => Models.E8 q
  | .F4 q => Models.F4 q
  | .G2 q _ => Models.G2 q
  | .twistedA r q _ _ => Models.TwistedA r q
  | .twistedD r q _ => Models.TwistedD r q
  | .twistedE6 q => Models.TwistedE6 q
  | .trialityD4 q => Models.TrialityD4 q
  | .suzuki m _ => Models.Suzuki m
  | .reeG2 m _ => Models.ReeG2 m
  | .reeF4 m _ => Models.ReeF4 m
  | .tits => Models.Tits
  | .sporadic s => s.Model

instance (i : Index) : Group i.Model := by
  cases i <;> unfold Model <;> infer_instance

end
end Index
end CFSG
