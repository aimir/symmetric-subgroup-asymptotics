import SymmetricSubgroupAsymptotics.CFSGTypeAOuterCardinality
import SymmetricSubgroupAsymptotics.CFSGProjectiveLinearGcdCardComparison
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphismsParameters
import SymmetricSubgroupAsymptotics.External.CFSG.Models.LieFamilies

/-! Actual outer automorphisms of the original PSL model satisfy the
finite-field bound 2*gcd(q-1,n)*|Aut(F)|. The original root geometry and
oriented collineation theorem are unchanged; only their central scalar
count is sharpened. No abstract automorphism lifting premise is added. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeAOuterGcdCardinality
open PrimitiveSocleRawStructure
open CFSGTypeARootGeometryAction CFSGTypeARootActionFaithfulness
variable {F:Type} [Field F] [Finite F] {n:ℕ}
abbrev PSL := Matrix.ProjectiveSpecialLinearGroup (Fin n) F

theorem outer_card_le_gcd (p:ℕ) [Fact p.Prime] [CharP F p] (hn:3≤n)
    [IsSimpleGroup (PSL (F:=F) (n:=n))] :
    Nat.card (Outer (PSL (F:=F) (n:=n))) ≤
      2*((Nat.card F-1).gcd n)*Nat.card (F≃+*F) := by
  let b:Fin n := ⟨0,by omega⟩
  let i:Fin n := ⟨1,by omega⟩
  let j:Fin n := ⟨2,by omega⟩
  letI : Nonempty (Fin n) := ⟨b⟩
  have hbi:b≠i := by intro h;have hh:=congrArg Fin.val h;dsimp [b,i] at hh;omega
  have hbj:b≠j := by intro h;have hh:=congrArg Fin.val h;dsimp [b,j] at hh;omega
  have hij:i≠j := by intro h;have hh:=congrArg Fin.val h;dsimp [i,j] at hh;omega
  have hcol := CFSGProjectiveCollineationCardinality.collineation_card_le_projective_mul_ringAut
    (F:=F) b i j hbi hbj hij
  have hpgl := CFSGProjectiveLinearGcdCardComparison.projective_card_le_gcd_mul_specialProjective
    (F:=F) (I:=Fin n)
  rw [Fintype.card_fin] at hpgl
  have haut : Nat.card (MulAut (PSL (F:=F) (n:=n))) ≤
      Nat.card (PSL (F:=F) (n:=n))*(2*((Nat.card F-1).gcd n)*Nat.card (F≃+*F)) := by
    calc
      _ ≤ 2*Nat.card (CFSGProjectiveFrameCoordinates.collineationGroup (F:=F) (n:=Fin n)) :=
        CFSGTypeAOrientedCollineation.automorphism_card_le_two_mul_collineation p hn
      _ ≤ 2*(Nat.card (Matrix.ProjGenLinGroup (Fin n) F)*Nat.card (F≃+*F)) :=
        Nat.mul_le_mul_left _ hcol
      _ ≤ 2*((((Nat.card F-1).gcd n)*Nat.card (PSL (F:=F) (n:=n)))*Nat.card (F≃+*F)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hpgl)
      _ = _ := by ring
  have hinner : Nat.card (Inner (PSL (F:=F) (n:=n)))=Nat.card (PSL (F:=F) (n:=n)) :=
    (Nat.card_congr (MonoidHom.ofInjective (CFSGTypeAOuterCardinality.conj_injective p hn)).toEquiv).symm
  have hcard := (Inner (PSL (F:=F) (n:=n))).card_mul_index
  change Nat.card (Inner (PSL (F:=F) (n:=n)))*Nat.card (Outer (PSL (F:=F) (n:=n)))=
    Nat.card (MulAut (PSL (F:=F) (n:=n))) at hcard
  rw [hinner] at hcard
  exact Nat.le_of_mul_le_mul_left (hcard.trans_le haut)
    (Nat.card_pos (α:=PSL (F:=F) (n:=n)))

theorem typeA_higher_outer_card_le_gcd (r:ℕ) (hr:2≤r) (q:CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.A r q)] :
    Nat.card (Outer (CFSG.Models.A r q)) ≤
      2*((q.order-1).gcd (r+1))*q.exponent := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  simpa only [q.card_field,CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q] using
    outer_card_le_gcd (F:=q.Field) q.prime (by omega : 3≤r+1)

end SymmetricSubgroupAsymptotics.CFSGTypeAOuterGcdCardinality
