import SymmetricSubgroupAsymptotics.External.CFSG.Parameters
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Chevalley
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Suzuki
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

namespace CFSG.Models
noncomputable section

/-- A_r(q) = SL_(r+1)(q) / Z(SL_(r+1)(q)). -/
abbrev A (r : ℕ) (q : PrimePower) :=
  Matrix.ProjectiveSpecialLinearGroup (Fin (r + 1)) q.Field

/- Serre's convention is Aᵢⱼ = αⱼ(hᵢ). In the pinned mathlib revision,
`CartanMatrix.B` has the double entry in row r-2, so its transpose is used
for B; likewise for C. Do not trust the upstream docstring's A rank shift:
`CartanMatrix.A r` is literally an r by r matrix, hence rank r. -/
abbrev B (r : ℕ) (q : PrimePower) := Chevalley.Projective (CartanMatrix.B r).transpose q.Field
abbrev C (r : ℕ) (q : PrimePower) := Chevalley.Projective (CartanMatrix.C r).transpose q.Field
abbrev D (r : ℕ) (q : PrimePower) := Chevalley.Projective (CartanMatrix.D r) q.Field
abbrev E6 (q : PrimePower) := Chevalley.Projective CartanMatrix.E₆ q.Field
abbrev E7 (q : PrimePower) := Chevalley.Projective CartanMatrix.E₇ q.Field
abbrev E8 (q : PrimePower) := Chevalley.Projective CartanMatrix.E₈ q.Field
abbrev F4 (q : PrimePower) := Chevalley.Projective CartanMatrix.F₄ q.Field
abbrev G2 (q : PrimePower) := Chevalley.Projective CartanMatrix.G₂ q.Field

/-- Diagram reversal for type A. -/
def reverseNode {r : ℕ} (i : Fin r) : Fin r := i.rev

/-- Exchange the two terminal fork nodes of D_r. -/
def dTwist {r : ℕ} (i : Fin r) : Fin r :=
  if h : 2 ≤ r then
    if i.val = r - 2 then ⟨r - 1, by omega⟩
    else if i.val = r - 1 then ⟨r - 2, by omega⟩ else i
  else i

/-- E6's involution in the precise numbering of the displayed Cartan matrix. -/
def e6Twist : Fin 6 → Fin 6 := ![5, 1, 4, 3, 2, 0]

/-- Triality cycles D4's three outer nodes 0,2,3 and fixes its central node 1. -/
def triality : Fin 4 → Fin 4 := ![2, 1, 3, 0]

/-- ²A_r(q), using GF(q²), derived fixed group and central quotient. -/
abbrev TwistedA (r : ℕ) (q : PrimePower) :=
  Chevalley.Twisted (CartanMatrix.A r) (q.Extension 2) reverseNode (fun _ => q.order)

/-- ²D_r(q), using GF(q²), derived fixed group and central quotient. -/
abbrev TwistedD (r : ℕ) (q : PrimePower) :=
  Chevalley.Twisted (CartanMatrix.D r) (q.Extension 2) dTwist (fun _ => q.order)

/-- ²E6(q), using GF(q²), derived fixed group and central quotient. -/
abbrev TwistedE6 (q : PrimePower) :=
  Chevalley.Twisted CartanMatrix.E₆ (q.Extension 2) e6Twist (fun _ => q.order)

/-- ³D4(q), using GF(q³), derived fixed group and central quotient. -/
abbrev TrialityD4 (q : PrimePower) :=
  Chevalley.Twisted (CartanMatrix.D 4) (q.Extension 3) triality (fun _ => q.order)

/-- Small Ree: node 0 is short in the pinned G2 Serre matrix.
The exceptional isogeny raises short-root parameters to the third power;
compose it with Frob^(m). -/
abbrev ReeG2 (m : ℕ) :=
  Chevalley.Twisted CartanMatrix.G₂ (GaloisField 3 (2 * m + 1)) reverseNode
    (fun i => if i.val = 0 then 3 ^ (m + 1) else 3 ^ m)

/-- Large Ree, including m=0 for the Tits construction. Nodes 0 and 1
are short in the pinned F4 Serre matrix. -/
abbrev ReeF4 (m : ℕ) :=
  Chevalley.Twisted CartanMatrix.F₄ (GaloisField 2 (2 * m + 1)) reverseNode
    (fun i => if i.val < 2 then 2 ^ (m + 1) else 2 ^ m)

/-- ²F4(2)′. `Chevalley.Twisted` already takes the derived subgroup,
so no second derived subgroup is accidentally substituted here. -/
abbrev Tits := ReeF4 0

end
end CFSG.Models
