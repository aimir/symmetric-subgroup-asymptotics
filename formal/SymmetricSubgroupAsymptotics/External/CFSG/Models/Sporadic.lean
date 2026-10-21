import SymmetricSubgroupAsymptotics.External.CFSG.Models.Monster
import SymmetricSubgroupAsymptotics.External.CFSG.Models.YGroups
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Mathieu22
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.M11
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.M12
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.M23
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.M24
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.HS
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.McL
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.Co2
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.J2
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.He
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.J1
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.J3
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.J4
import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.Co3
import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.Co1
import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.Suz
import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.HN
import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.Th
import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.ON
import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.Ly
import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.Ru
import Mathlib.Tactic.DeriveFintype

namespace CFSG

/-- Exactly the 26 sporadic names. The Tits group has its own classification branch. -/
inductive Sporadic
  | m11 | m12 | m22 | m23 | m24
  | j1 | j2 | j3 | j4
  | co1 | co2 | co3 | fi22 | fi23 | fi24Prime
  | hs | mcl | he | ru | suz | onan | hn | ly | th | babyMonster | monster
  deriving DecidableEq, Fintype

namespace Sporadic

/-- Every case unfolds to a concrete presentation, subgroup, or central quotient. -/
def Model : Sporadic → Type
  | .m11 => Models.Presentations.M11.Model
  | .m12 => Models.Presentations.M12.Model
  | .m22 => Models.Mathieu22
  | .m23 => Models.Presentations.M23.Model
  | .m24 => Models.Presentations.M24.Model
  | .j1 => Models.Presentations.J1.Model
  | .j2 => Models.Presentations.J2.Model
  | .j3 => Models.Presentations.J3.Model
  | .j4 => Models.Presentations.J4.Model
  | .co1 => Models.MatrixGroups.Co1.Model
  | .co2 => Models.Presentations.Co2.Model
  | .co3 => Models.MatrixGroups.Co3.Model
  | .fi22 => Models.Fischer22
  | .fi23 => Models.Fischer23
  | .fi24Prime => Models.Fischer24Prime
  | .hs => Models.Presentations.HS.Model
  | .mcl => Models.Presentations.McL.Model
  | .he => Models.Presentations.He.Model
  | .ru => Models.MatrixGroups.Ru.Model
  | .suz => Models.MatrixGroups.Suz.Model
  | .onan => Models.MatrixGroups.ON.Model
  | .hn => Models.MatrixGroups.HN.Model
  | .ly => Models.MatrixGroups.Ly.Model
  | .th => Models.MatrixGroups.Th.Model
  | .babyMonster => Models.BabyMonster
  | .monster => Models.Monster

noncomputable instance (s : Sporadic) : Group s.Model := by
  cases s <;> unfold Model <;> infer_instance

theorem card : Fintype.card Sporadic = 26 := by decide

end Sporadic
end CFSG
