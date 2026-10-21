import SymmetricSubgroupAsymptotics.CFSGInvolutionOrder
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Sporadic

/-! Eleven literal sporadic presentations have even order whenever they
are noncommutative. Only their displayed first involutory relator and
actual two-generator presentation are used. No order or identification
certificate is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

theorem m11_even_card
    (hn : ¬ IsMulCommutative CFSG.Models.Presentations.M11.Model) :
    Even (Nat.card CFSG.Models.Presentations.M11.Model) := by
  apply presented_pair_even_card CFSG.Models.Presentations.M11.relators
  · exact List.mem_cons_self
  · exact hn

theorem m12_even_card
    (hn : ¬ IsMulCommutative CFSG.Models.Presentations.M12.Model) :
    Even (Nat.card CFSG.Models.Presentations.M12.Model) := by
  apply presented_pair_even_card CFSG.Models.Presentations.M12.relators
  · exact List.mem_cons_self
  · exact hn

theorem m23_even_card
    (hn : ¬ IsMulCommutative CFSG.Models.Presentations.M23.Model) :
    Even (Nat.card CFSG.Models.Presentations.M23.Model) := by
  apply presented_pair_even_card CFSG.Models.Presentations.M23.relators
  · exact List.mem_cons_self
  · exact hn

theorem m24_even_card
    (hn : ¬ IsMulCommutative CFSG.Models.Presentations.M24.Model) :
    Even (Nat.card CFSG.Models.Presentations.M24.Model) := by
  apply presented_pair_even_card CFSG.Models.Presentations.M24.relators
  · exact List.mem_cons_self
  · exact hn

theorem j1_even_card
    (hn : ¬ IsMulCommutative CFSG.Models.Presentations.J1.Model) :
    Even (Nat.card CFSG.Models.Presentations.J1.Model) := by
  apply presented_pair_even_card CFSG.Models.Presentations.J1.relators
  · exact List.mem_cons_self
  · exact hn

theorem j2_even_card
    (hn : ¬ IsMulCommutative CFSG.Models.Presentations.J2.Model) :
    Even (Nat.card CFSG.Models.Presentations.J2.Model) := by
  apply presented_pair_even_card CFSG.Models.Presentations.J2.relators
  · exact List.mem_cons_self
  · exact hn

theorem j3_even_card
    (hn : ¬ IsMulCommutative CFSG.Models.Presentations.J3.Model) :
    Even (Nat.card CFSG.Models.Presentations.J3.Model) := by
  apply presented_pair_even_card CFSG.Models.Presentations.J3.relators
  · exact List.mem_cons_self
  · exact hn

theorem co2_even_card
    (hn : ¬ IsMulCommutative CFSG.Models.Presentations.Co2.Model) :
    Even (Nat.card CFSG.Models.Presentations.Co2.Model) := by
  apply presented_pair_even_card CFSG.Models.Presentations.Co2.relators
  · exact List.mem_cons_self
  · exact hn

theorem hs_even_card
    (hn : ¬ IsMulCommutative CFSG.Models.Presentations.HS.Model) :
    Even (Nat.card CFSG.Models.Presentations.HS.Model) := by
  apply presented_pair_even_card CFSG.Models.Presentations.HS.relators
  · exact List.mem_cons_self
  · exact hn

theorem mcl_even_card
    (hn : ¬ IsMulCommutative CFSG.Models.Presentations.McL.Model) :
    Even (Nat.card CFSG.Models.Presentations.McL.Model) := by
  apply presented_pair_even_card CFSG.Models.Presentations.McL.relators
  · exact List.mem_cons_self
  · exact hn

theorem he_even_card
    (hn : ¬ IsMulCommutative CFSG.Models.Presentations.He.Model) :
    Even (Nat.card CFSG.Models.Presentations.He.Model) := by
  apply presented_pair_even_card CFSG.Models.Presentations.He.relators
  · exact List.mem_cons_self
  · exact hn

end SymmetricSubgroupAsymptotics.CFSGReduction
