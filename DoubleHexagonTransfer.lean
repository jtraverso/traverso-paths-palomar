module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# A potential for the signed double-hexagon certificate

The roots, triangles and coefficients come from Juan Pablo Traverso Gianini,
`SignedCertificate/DoubleHexagon.lean` at 673c6d4118b5679783bafa7606fd2c611161a254.
A triangle is projected onto the nine roots, with every auxiliary vertex
sent to `none`. Edges with an auxiliary endpoint have weight zero.
-/

@[expose] public section

open scoped BigOperators

namespace DoubleHexagonTransfer

abbrev Roots := Fin 9
abbrev Edge := Sym2 Roots
abbrev ProjectedTriangle := Fin 3 → Option Roots

def rim : Finset Edge :=
  {s(0, 3), s(3, 1), s(1, 4), s(4, 2), s(2, 5), s(5, 0),
    s(0, 6), s(6, 1), s(1, 7), s(7, 2), s(2, 8), s(8, 0)}

def core : Finset Edge := {s(0, 1), s(1, 2), s(0, 2)}

def rootEdges : Finset Edge := rim ∪ core

def rootSide : Option Roots → Option Roots → Finset Edge
  | some a, some b => {s(a, b)}
  | _, _ => ∅

def sides (t : ProjectedTriangle) : Finset Edge :=
  rootSide (t 0) (t 1) ∪ rootSide (t 1) (t 2) ∪ rootSide (t 0) (t 2)

/-- A triangle from any host inducing `rootEdges` on the roots satisfies this condition. -/
def legal (t : ProjectedTriangle) : Prop := sides t ⊆ rootEdges

def hasAuxiliary (t : ProjectedTriangle) : Bool :=
  t 0 == none || t 1 == none || t 2 == none

def edgeWeight (e : Edge) : ℤ := if e ∈ rim then 2 else if e ∈ core then -1 else 0

def indicator (S : Finset Edge) (e : Edge) : ℤ := if e ∈ S then 1 else 0

def potential (x : Edge → ℤ) : ℤ := ∑ e ∈ rootEdges, edgeWeight e * x e

def charge (t : ProjectedTriangle) : ℤ := potential (indicator (sides t))

theorem rim_potential : potential (indicator rim) = 24 := by decide

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
private theorem charge_bound_tuple (a : Option Roots) : ∀ b c : Option Roots,
    legal ![a, b, c] → |charge ![a, b, c]| ≤ if hasAuxiliary ![a, b, c] then 2 else 3 := by
  cases a with
  | none =>
    unfold legal charge potential hasAuxiliary rootEdges edgeWeight indicator sides rootSide rim core
    decide
  | some a =>
    fin_cases a <;>
      unfold legal charge potential hasAuxiliary rootEdges edgeWeight indicator sides rootSide rim core <;>
      decide

/-- The complete local check has at most `10³` states, independently of host size. -/
theorem charge_bound : ∀ t : ProjectedTriangle,
    legal t → |charge t| ≤ if hasAuxiliary t then 2 else 3 := by
  intro t
  have ht : ![t 0, t 1, t 2] = t := by
    funext i
    fin_cases i <;> rfl
  rw [← ht]
  exact charge_bound_tuple _ _ _

/-- The potential telescopes along the certificate, and auxiliary moves lose
at least one unit of potential capacity per unit of signed weight. -/
theorem weight_and_auxiliary_bound {ι : Type*} [Fintype ι]
    (tri : ι → ProjectedTriangle) (coeff : ι → ℤ)
    (hlegal : ∀ i, legal (tri i))
    (balance : ∀ e ∈ rootEdges, indicator rim e = ∑ i, coeff i * indicator (sides (tri i)) e) :
    (24 : ℤ) + (∑ i, if hasAuxiliary (tri i) then (coeff i).natAbs else 0 : ℕ) ≤
      3 * (∑ i, (coeff i).natAbs : ℕ) := by
  have htel : potential (indicator rim) = ∑ i, coeff i * charge (tri i) := by
    calc
      potential (indicator rim) = ∑ e ∈ rootEdges,
          edgeWeight e * (∑ i, coeff i * indicator (sides (tri i)) e) := by
        unfold potential
        exact Finset.sum_congr rfl fun e he => congrArg (edgeWeight e * ·) (balance e he)
      _ = ∑ i, coeff i * charge (tri i) := by
        simp only [charge, potential, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro e _
        ring
  have hstep (i : ι) : coeff i * charge (tri i) +
      (if hasAuxiliary (tri i) then ((coeff i).natAbs : ℤ) else 0) ≤
      3 * ((coeff i).natAbs : ℤ) := by
    have hb := charge_bound (tri i) (hlegal i)
    have hmul : coeff i * charge (tri i) ≤ |coeff i| * |charge (tri i)| := by
      rw [← abs_mul]
      exact le_abs_self _
    rw [← Int.natCast_natAbs] at hmul
    have hpaid := hmul.trans (mul_le_mul_of_nonneg_left hb
      (Int.natCast_nonneg (coeff i).natAbs))
    split_ifs with ha <;> simp only [ha, Bool.false_eq_true, ite_false, ite_true] at hpaid ⊢ <;> omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hstep i)
  rw [Finset.sum_add_distrib, ← htel, rim_potential, ← Finset.mul_sum] at hsum
  push_cast at hsum ⊢
  exact hsum

theorem weight_lower_bound {ι : Type*} [Fintype ι]
    (tri : ι → ProjectedTriangle) (coeff : ι → ℤ)
    (hlegal : ∀ i, legal (tri i))
    (balance : ∀ e ∈ rootEdges, indicator rim e = ∑ i, coeff i * indicator (sides (tri i)) e) :
    8 ≤ ∑ i, (coeff i).natAbs := by
  have h := weight_and_auxiliary_bound tri coeff hlegal balance
  omega

def projectRoot {A : Type*} : Roots ⊕ A → Option Roots
  | .inl i => some i
  | .inr _ => none

def physicalSides {A : Type*} [DecidableEq A] (t : Fin 3 → Roots ⊕ A) :
    Finset (Sym2 (Roots ⊕ A)) := {s(t 0, t 1), s(t 1, t 2), s(t 0, t 2)}

/-- Projection preserves precisely the incidences with physical root edges. -/
theorem root_edge_membership {A : Type*} [DecidableEq A]
    (e : Edge) (t : Fin 3 → Roots ⊕ A) :
    e ∈ sides (projectRoot ∘ t) ↔ e.map Sum.inl ∈ physicalSides t := by
  have side (a b : Roots ⊕ A) : e ∈ rootSide (projectRoot a) (projectRoot b) ↔
      e.map Sum.inl = s(a, b) := by
    induction e using Sym2.ind with
    | _ x y =>
      cases a <;> cases b <;>
        simp [projectRoot, rootSide, Sym2.map_mk, Prod.mk.injEq]
  simp [sides, physicalSides, side]

/-- The bound holds in any physical extension with the same induced root edges.
A signed physical certificate supplies the equalities on all root edges. -/
theorem physical_certificate_budget {A ι : Type*} [DecidableEq A] [Fintype ι]
    (tri : ι → Fin 3 → Roots ⊕ A) (coeff : ι → ℤ)
    (hroot : ∀ (i : ι) (e : Edge), e.map Sum.inl ∈ physicalSides (tri i) → e ∈ rootEdges)
    (balance : ∀ e ∈ rootEdges,
      indicator rim e = ∑ i, coeff i * (if e.map Sum.inl ∈ physicalSides (tri i) then 1 else 0)) :
    (24 : ℤ) + (∑ i, if hasAuxiliary (projectRoot ∘ tri i) then (coeff i).natAbs else 0 : ℕ) ≤
      3 * (∑ i, (coeff i).natAbs : ℕ) := by
  apply weight_and_auxiliary_bound (fun i => projectRoot ∘ tri i) coeff
  · intro i e he
    exact hroot i e ((root_edge_membership e (tri i)).mp he)
  · intro e he
    simpa only [indicator, root_edge_membership] using balance e he

def rootTriangle : Fin 7 → Fin 3 → Roots :=
  ![![0, 3, 1], ![1, 4, 2], ![2, 5, 0], ![0, 6, 1], ![1, 7, 2], ![2, 8, 0], ![0, 1, 2]]

def triC (i : Fin 7) (j : Fin 3) : Option Roots := some (rootTriangle i j)

def coef : Fin 7 → ℤ := ![1, 1, 1, 1, 1, 1, -2]

def rootPart : Roots → Fin 2 := ![0, 0, 1, 1, 0, 1, 1, 0, 1]

/-- The published certificate attains the bound, with only mixed triangles. -/
theorem published_certificate :
    (∀ i, legal (triC i) ∧
      (rootPart (rootTriangle i 0) ≠ rootPart (rootTriangle i 1) ∨
        rootPart (rootTriangle i 1) ≠ rootPart (rootTriangle i 2))) ∧
    (∀ e ∈ rootEdges, indicator rim e = ∑ i, coef i * indicator (sides (triC i)) e) ∧
    (∑ i, (coef i).natAbs) = 8 := by
  unfold legal triC rootTriangle rootPart sides rootSide rootEdges rim core indicator coef
  decide

end DoubleHexagonTransfer
