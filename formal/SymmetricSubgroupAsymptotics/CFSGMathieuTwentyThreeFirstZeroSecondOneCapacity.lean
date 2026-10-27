import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreePackedPrefixCertificate

/-! ONE actual prefix first0/second1, exactly960 tails. Data are not a
proof until scalar_certificate passes the primary capped Lean gate.
The whitelist is literal and variable; no uniform capacity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeFirstZeroSecondOneCapacity
open CFSGMathieuTwentyThreeStabilizerTransversalCover CFSGMathieuTwentyThreeNormalizedFibreChart
open CFSGMathieuTwentyThreePackedPrefixCertificate

def selectedFirst : First := ⟨0,by decide⟩
def selectedSecond : Second := ⟨1,by decide⟩

private def failureK2 (l m : ℕ) : ℕ :=
  match l with
  | 5 => (match m with | 3 => 23 | 4 => 1 | _ => 1)
  | 6 => (match m with | 3 => 3 | 4 => 1 | _ => 23)
  | 7 => (match m with | 3 => 1 | 4 => 23 | _ => 1)
  | 8 => (match m with | 3 => 1 | 4 => 1 | _ => 23)
  | 9 => (match m with | 3 => 23 | 4 => 1 | _ => 1)
  | 10 => (match m with | 3 => 24 | 4 => 1 | _ => 1)
  | 11 => (match m with | 3 => 3 | 4 => 23 | _ => 1)
  | 12 => (match m with | 3 => 1 | 4 => 1 | _ => 23)
  | 13 => (match m with | 3 => 1 | 4 => 1 | _ => 23)
  | 14 => (match m with | 3 => 1 | 4 => 1 | _ => 23)
  | 15 => (match m with | 3 => 23 | 4 => 1 | _ => 1)
  | 16 => (match m with | 3 => 1 | 4 => 1 | _ => 23)
  | 17 => (match m with | 3 => 1 | 4 => 23 | _ => 1)
  | 18 => (match m with | 3 => 1 | 4 => 1 | _ => 23)
  | 19 => (match m with | 3 => 1 | 4 => 23 | _ => 1)
  | 20 => (match m with | 3 => 1 | 4 => 1 | _ => 23)
  | _ => 0

private def failureK3 (l m : ℕ) : ℕ :=
  match l with
  | 5 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 6 => (match m with | 3 => 1 | 4 => 1 | _ => 23)
  | 7 => (match m with | 3 => 3 | 4 => 1 | _ => 1)
  | 8 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 9 => (match m with | 3 => 23 | 4 => 1 | _ => 1)
  | 10 => (match m with | 3 => 1 | 4 => 3 | _ => 1)
  | 11 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 12 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 13 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 14 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 15 => (match m with | 3 => 23 | 4 => 1 | _ => 1)
  | 16 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 17 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 18 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 19 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 20 => (match m with | 3 => 1 | 4 => 1 | _ => 24)
  | _ => 0

private def failureK4 (l m : ℕ) : ℕ :=
  match l with
  | 5 => (match m with | 3 => 1 | 4 => 1 | _ => 3)
  | 6 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 7 => (match m with | 3 => 1 | 4 => 1 | _ => 23)
  | 8 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 9 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 10 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 11 => (match m with | 3 => 1 | 4 => 3 | _ => 1)
  | 12 => (match m with | 3 => 24 | 4 => 1 | _ => 1)
  | 13 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 14 => (match m with | 3 => 23 | 4 => 1 | _ => 1)
  | 15 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 16 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 17 => (match m with | 3 => 1 | 4 => 1 | _ => 23)
  | 18 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 19 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 20 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | _ => 0

private def failureK5 (l m : ℕ) : ℕ :=
  match l with
  | 5 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 6 => (match m with | 3 => 1 | 4 => 3 | _ => 1)
  | 7 => (match m with | 3 => 1 | 4 => 3 | _ => 1)
  | 8 => (match m with | 3 => 3 | 4 => 1 | _ => 1)
  | 9 => (match m with | 3 => 23 | 4 => 23 | _ => 23)
  | 10 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 11 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 12 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 13 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 14 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 15 => (match m with | 3 => 1 | 4 => 1 | _ => 3)
  | 16 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 17 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 18 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 19 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 20 => (match m with | 3 => 1 | 4 => 3 | _ => 1)
  | _ => 0

private def failureK6 (l m : ℕ) : ℕ :=
  match l with
  | 5 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 6 => (match m with | 3 => 1 | 4 => 3 | _ => 1)
  | 7 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 8 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 9 => (match m with | 3 => 1 | 4 => 1 | _ => 3)
  | 10 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 11 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 12 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 13 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 14 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 15 => (match m with | 3 => 1 | 4 => 1 | _ => 23)
  | 16 => (match m with | 3 => 23 | 4 => 1 | _ => 1)
  | 17 => (match m with | 3 => 1 | 4 => 3 | _ => 1)
  | 18 => (match m with | 3 => 3 | 4 => 1 | _ => 23)
  | 19 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 20 => (match m with | 3 => 1 | 4 => 3 | _ => 1)
  | _ => 0

private def failureK7 (l m : ℕ) : ℕ :=
  match l with
  | 5 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 6 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 7 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 8 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 9 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 10 => (match m with | 3 => 1 | 4 => 23 | _ => 1)
  | 11 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 12 => (match m with | 3 => 1 | 4 => 23 | _ => 1)
  | 13 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 14 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 15 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 16 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 17 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 18 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 19 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 20 => (match m with | 3 => 1 | 4 => 1 | _ => 23)
  | _ => 0

private def failureK8 (l m : ℕ) : ℕ :=
  match l with
  | 5 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 6 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 7 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 8 => (match m with | 3 => 3 | 4 => 1 | _ => 1)
  | 9 => (match m with | 3 => 25 | 4 => 1 | _ => 1)
  | 10 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 11 => (match m with | 3 => 1 | 4 => 1 | _ => 3)
  | 12 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 13 => (match m with | 3 => 23 | 4 => 1 | _ => 1)
  | 14 => (match m with | 3 => 1 | 4 => 1 | _ => 3)
  | 15 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 16 => (match m with | 3 => 1 | 4 => 23 | _ => 1)
  | 17 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 18 => (match m with | 3 => 3 | 4 => 1 | _ => 1)
  | 19 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 20 => (match m with | 3 => 1 | 4 => 3 | _ => 1)
  | _ => 0

private def failureK9 (l m : ℕ) : ℕ :=
  match l with
  | 5 => (match m with | 3 => 1 | 4 => 1 | _ => 23)
  | 6 => (match m with | 3 => 3 | 4 => 1 | _ => 1)
  | 7 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 8 => (match m with | 3 => 1 | 4 => 3 | _ => 1)
  | 9 => (match m with | 3 => 1 | 4 => 23 | _ => 1)
  | 10 => (match m with | 3 => 3 | 4 => 1 | _ => 1)
  | 11 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 12 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 13 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 14 => (match m with | 3 => 1 | 4 => 1 | _ => 23)
  | 15 => (match m with | 3 => 1 | 4 => 3 | _ => 1)
  | 16 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 17 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 18 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 19 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 20 => (match m with | 3 => 3 | 4 => 1 | _ => 1)
  | _ => 0

private def failureK10 (l m : ℕ) : ℕ :=
  match l with
  | 5 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 6 => (match m with | 3 => 1 | 4 => 23 | _ => 3)
  | 7 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 8 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 9 => (match m with | 3 => 3 | 4 => 23 | _ => 1)
  | 10 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 11 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 12 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 13 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 14 => (match m with | 3 => 1 | 4 => 4 | _ => 1)
  | 15 => (match m with | 3 => 3 | 4 => 1 | _ => 1)
  | 16 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 17 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 18 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 19 => (match m with | 3 => 1 | 4 => 1 | _ => 3)
  | 20 => (match m with | 3 => 1 | 4 => 1 | _ => 23)
  | _ => 0

private def failureK11 (l m : ℕ) : ℕ :=
  match l with
  | 5 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 6 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 7 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 8 => (match m with | 3 => 3 | 4 => 1 | _ => 1)
  | 9 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 10 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 11 => (match m with | 3 => 1 | 4 => 1 | _ => 3)
  | 12 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 13 => (match m with | 3 => 23 | 4 => 1 | _ => 1)
  | 14 => (match m with | 3 => 1 | 4 => 1 | _ => 3)
  | 15 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 16 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 17 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 18 => (match m with | 3 => 3 | 4 => 1 | _ => 1)
  | 19 => (match m with | 3 => 23 | 4 => 1 | _ => 1)
  | 20 => (match m with | 3 => 1 | 4 => 3 | _ => 23)
  | _ => 0

private def failureK12 (l m : ℕ) : ℕ :=
  match l with
  | 5 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 6 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 7 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 8 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 9 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 10 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 11 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 12 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 13 => (match m with | 3 => 1 | 4 => 1 | _ => 23)
  | 14 => (match m with | 3 => 23 | 4 => 1 | _ => 1)
  | 15 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 16 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 17 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 18 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 19 => (match m with | 3 => 23 | 4 => 1 | _ => 1)
  | 20 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | _ => 0

private def failureK13 (l m : ℕ) : ℕ :=
  match l with
  | 5 => (match m with | 3 => 1 | 4 => 1 | _ => 3)
  | 6 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 7 => (match m with | 3 => 1 | 4 => 1 | _ => 3)
  | 8 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 9 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 10 => (match m with | 3 => 23 | 4 => 1 | _ => 1)
  | 11 => (match m with | 3 => 1 | 4 => 3 | _ => 1)
  | 12 => (match m with | 3 => 23 | 4 => 1 | _ => 1)
  | 13 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 14 => (match m with | 3 => 3 | 4 => 1 | _ => 1)
  | 15 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 16 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 17 => (match m with | 3 => 1 | 4 => 1 | _ => 3)
  | 18 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 19 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 20 => (match m with | 3 => 1 | 4 => 23 | _ => 1)
  | _ => 0

private def failureK14 (l m : ℕ) : ℕ :=
  match l with
  | 5 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 6 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 7 => (match m with | 3 => 1 | 4 => 1 | _ => 23)
  | 8 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 9 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 10 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 11 => (match m with | 3 => 1 | 4 => 23 | _ => 1)
  | 12 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 13 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 14 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 15 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 16 => (match m with | 3 => 1 | 4 => 23 | _ => 1)
  | 17 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 18 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 19 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 20 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | _ => 0

private def failureK15 (l m : ℕ) : ℕ :=
  match l with
  | 5 => (match m with | 3 => 1 | 4 => 1 | _ => 3)
  | 6 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 7 => (match m with | 3 => 1 | 4 => 1 | _ => 3)
  | 8 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 9 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 10 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 11 => (match m with | 3 => 1 | 4 => 3 | _ => 1)
  | 12 => (match m with | 3 => 23 | 4 => 1 | _ => 1)
  | 13 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 14 => (match m with | 3 => 3 | 4 => 1 | _ => 1)
  | 15 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 16 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 17 => (match m with | 3 => 1 | 4 => 1 | _ => 3)
  | 18 => (match m with | 3 => 1 | 4 => 23 | _ => 1)
  | 19 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 20 => (match m with | 3 => 1 | 4 => 1 | _ => 23)
  | _ => 0

private def failureK16 (l m : ℕ) : ℕ :=
  match l with
  | 5 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 6 => (match m with | 3 => 3 | 4 => 1 | _ => 23)
  | 7 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 8 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 9 => (match m with | 3 => 1 | 4 => 3 | _ => 23)
  | 10 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 11 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 12 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 13 => (match m with | 3 => 1 | 4 => 3 | _ => 1)
  | 14 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 15 => (match m with | 3 => 1 | 4 => 3 | _ => 1)
  | 16 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 17 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 18 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 19 => (match m with | 3 => 1 | 4 => 3 | _ => 1)
  | 20 => (match m with | 3 => 23 | 4 => 1 | _ => 1)
  | _ => 0

private def failureK17 (l m : ℕ) : ℕ :=
  match l with
  | 5 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 6 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 7 => (match m with | 3 => 1 | 4 => 1 | _ => 23)
  | 8 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 9 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 10 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 11 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 12 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 13 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 14 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 15 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 16 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 17 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 18 => (match m with | 3 => 1 | 4 => 1 | _ => 23)
  | 19 => (match m with | 3 => 23 | 4 => 1 | _ => 1)
  | 20 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | _ => 0

private def failureK18 (l m : ℕ) : ℕ :=
  match l with
  | 5 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 6 => (match m with | 3 => 1 | 4 => 1 | _ => 3)
  | 7 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 8 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 9 => (match m with | 3 => 3 | 4 => 1 | _ => 1)
  | 10 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 11 => (match m with | 3 => 1 | 4 => 1 | _ => 23)
  | 12 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 13 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 14 => (match m with | 3 => 1 | 4 => 3 | _ => 1)
  | 15 => (match m with | 3 => 3 | 4 => 1 | _ => 1)
  | 16 => (match m with | 3 => 1 | 4 => 23 | _ => 1)
  | 17 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 18 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 19 => (match m with | 3 => 1 | 4 => 1 | _ => 3)
  | 20 => (match m with | 3 => 1 | 4 => 1 | _ => 23)
  | _ => 0

private def failureK19 (l m : ℕ) : ℕ :=
  match l with
  | 5 => (match m with | 3 => 1 | 4 => 1 | _ => 3)
  | 6 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 7 => (match m with | 3 => 1 | 4 => 23 | _ => 3)
  | 8 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 9 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 10 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 11 => (match m with | 3 => 1 | 4 => 3 | _ => 1)
  | 12 => (match m with | 3 => 23 | 4 => 1 | _ => 1)
  | 13 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 14 => (match m with | 3 => 3 | 4 => 23 | _ => 1)
  | 15 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 16 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 17 => (match m with | 3 => 1 | 4 => 1 | _ => 3)
  | 18 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 19 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 20 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | _ => 0

private def failureK20 (l m : ℕ) : ℕ :=
  match l with
  | 5 => (match m with | 3 => 1 | 4 => 3 | _ => 1)
  | 6 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 7 => (match m with | 3 => 4 | 4 => 1 | _ => 1)
  | 8 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 9 => (match m with | 3 => 3 | 4 => 1 | _ => 1)
  | 10 => (match m with | 3 => 1 | 4 => 23 | _ => 1)
  | 11 => (match m with | 3 => 1 | 4 => 23 | _ => 1)
  | 12 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 13 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 14 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 15 => (match m with | 3 => 1 | 4 => 1 | _ => 23)
  | 16 => (match m with | 3 => 3 | 4 => 1 | _ => 1)
  | 17 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 18 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 19 => (match m with | 3 => 1 | 4 => 1 | _ => 3)
  | 20 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | _ => 0

private def failureK21 (l m : ℕ) : ℕ :=
  match l with
  | 5 => (match m with | 3 => 1 | 4 => 3 | _ => 1)
  | 6 => (match m with | 3 => 1 | 4 => 1 | _ => 23)
  | 7 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 8 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 9 => (match m with | 3 => 23 | 4 => 1 | _ => 1)
  | 10 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 11 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 12 => (match m with | 3 => 1 | 4 => 3 | _ => 1)
  | 13 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 14 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 15 => (match m with | 3 => 23 | 4 => 1 | _ => 1)
  | 16 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 17 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 18 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 19 => (match m with | 3 => 1 | 4 => 1 | _ => 1)
  | 20 => (match m with | 3 => 1 | 4 => 1 | _ => 24)
  | _ => 0

def failure (k l m : ℕ) : ℕ :=
  match k with
  | 2 => failureK2 l m
  | 3 => failureK3 l m
  | 4 => failureK4 l m
  | 5 => failureK5 l m
  | 6 => failureK6 l m
  | 7 => failureK7 l m
  | 8 => failureK8 l m
  | 9 => failureK9 l m
  | 10 => failureK10 l m
  | 11 => failureK11 l m
  | 12 => failureK12 l m
  | 13 => failureK13 l m
  | 14 => failureK14 l m
  | 15 => failureK15 l m
  | 16 => failureK16 l m
  | 17 => failureK17 l m
  | 18 => failureK18 l m
  | 19 => failureK19 l m
  | 20 => failureK20 l m
  | 21 => failureK21 l m
  | _ => 0

def whitelist : List RawTail := []

/-- Single Boolean reflection check; no proof-bearing finite iteration. -/
theorem scalar_certificate : batchCheck 0 1 failure whitelist = true := by
  decide +kernel

noncomputable def acceptedElements : Finset (Equiv.Perm (Fin 23)) :=
  CFSGMathieuTwentyThreePackedPrefixCertificate.acceptedElements selectedFirst selectedSecond whitelist

theorem accepts_mem_acceptedElements (c : Code)
    (hfirst : c.1.1 = selectedFirst) (hsecond : c.1.2 = selectedSecond)
    (hc : CFSGMathieuTwentyThreeProductNecessaryRelations.Accepts (decodeAtZero c).val) :
    (decodeAtZero c).val ∈ acceptedElements :=
  CFSGMathieuTwentyThreePackedPrefixCertificate.accepts_mem_acceptedElements
    selectedFirst selectedSecond failure whitelist scalar_certificate c hfirst hsecond hc

theorem acceptedElements_card_le_count : acceptedElements.card ≤ 0 :=
  CFSGMathieuTwentyThreePackedPrefixCertificate.acceptedElements_card_le_length
    selectedFirst selectedSecond whitelist

theorem acceptingImages_card_le_count :
    Nat.card (acceptingImages selectedFirst selectedSecond) ≤ 0 :=
  CFSGMathieuTwentyThreePackedPrefixCertificate.acceptingImages_card_le_length
    selectedFirst selectedSecond failure whitelist scalar_certificate

theorem selected_prefix_excluded (c : Code)
    (hfirst : c.1.1 = selectedFirst) (hsecond : c.1.2 = selectedSecond) :
    ¬ CFSGMathieuTwentyThreeProductNecessaryRelations.Accepts (decodeAtZero c).val := by
  intro hc
  have hm := accepts_mem_acceptedElements c hfirst hsecond hc
  change _ ∈ (∅ : Finset (Equiv.Perm (Fin 23))) at hm
  exact Finset.notMem_empty _ hm

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeFirstZeroSecondOneCapacity
