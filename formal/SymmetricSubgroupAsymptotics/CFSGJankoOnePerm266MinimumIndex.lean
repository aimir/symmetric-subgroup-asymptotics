import SymmetricSubgroupAsymptotics.CFSGJankoOnePerm266Relations
import SymmetricSubgroupAsymptotics.CFSGJankoOneLiteralRepresentation
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex
import Mathlib.GroupTheory.Index

/-! Future symbolic consumer of the complete literal five-row packet.
The imported Relations source is deliberately not emitted before the pilot
passes. Once that closed leaf exists, no order, model identification, source
simplicity or representation premise is needed for this index upper bound. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGJankoOnePerm266MinimumIndex
open PrimitiveSocleRawStructure
open CFSGJankoOnePerm266Pilot CFSGJankoOneLiteralRepresentation

abbrev G := CFSG.Models.Presentations.J1.Model

def rho : G →* Equiv.Perm (Fin 266) :=
  representation CFSGJankoOnePerm266Relations.packet

theorem rho_pinnedX : rho CFSGJankoOnePresentationGenerators.pinnedX = a :=
  representation_pinnedX CFSGJankoOnePerm266Relations.packet

theorem faithful [IsSimpleGroup G] : Function.Injective rho :=
  representation_injective CFSGJankoOnePerm266Relations.packet a_ne_one

theorem least_index_le_twoSixtySix (ell : ℕ) (hell : LeastProperIndex G ell) :
    ell ≤ 266 := by
  letI : MulAction G (Fin 266) := MulAction.compHom (Fin 266) rho
  let H : Subgroup G := MulAction.stabilizer G (0 : Fin 266)
  have hH : H ≠ ⊤ := by
    intro ht
    have hm : CFSGJankoOnePresentationGenerators.pinnedX ∈ H := by
      rw [ht]
      trivial
    have he : rho CFSGJankoOnePresentationGenerators.pinnedX 0 = 0 := hm
    rw [rho_pinnedX] at he
    have hv := congrArg (fun i : Fin 266 => i.val) he
    change (a 0).val = 0 at hv
    rw [a_zero_value] at hv
    exact (by decide : (238 : ℕ) ≠ 0) hv
  have hi : H.index ≤ 266 := by
    simpa only [Nat.card_fin] using
      (MulAction.index_stabilizer G (0 : Fin 266)).trans_le (Set.ncard_le_card _)
  exact (hell.2 H hH).trans hi

end SymmetricSubgroupAsymptotics.CFSGJankoOnePerm266MinimumIndex
