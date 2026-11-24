module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.Linarith

/-!
# A graph of Newton slope blocks for the truncation bound

Vertices are slope components; the edge `j → i` is the `(i,j)` block of an
endomorphism. This file verifies the valuation estimate and assembles the
transported edges. The lattice hypotheses in `slope_graph_bound` are supplied
in the cyclic Dieudonné case by Lau–Nicole–Vasiu, Proposition 5.12 and
Notation 5.11 (arXiv:0912.0506). The passage to the isomorphism number uses
their Theorem 1.6 and specialization theorem outside this file.
-/

open scoped BigOperators

@[expose] public section

namespace TraversoSlopeGraph

/-- An integral block loses at most its source threshold in valuation.
The arbitrary lower bound `a` also covers vectors of infinite valuation. -/
theorem block_lower_bound {X Y : Type*}
    (wx : X → WithTop ℚ) (wy : Y → WithTop ℚ)
    (sx : ℤ → X → X) (sy : ℤ → Y → Y) (u : X → Y) (β : ℚ)
    (hsx : ∀ s x, wx (sx s x) = wx x + ((s : ℚ) : WithTop ℚ))
    (hsy : ∀ s y, wy (sy s y) = wy y + ((s : ℚ) : WithTop ℚ))
    (hu : ∀ s x, u (sx s x) = sy s (u x))
    (hint : ∀ x, ((β - 1 : ℚ) : WithTop ℚ) < wx x → (0 : WithTop ℚ) ≤ wy (u x))
    (x : X) (a : ℚ) (ha : (a : WithTop ℚ) ≤ wx x) :
    ((a - β : ℚ) : WithTop ℚ) ≤ wy (u x) := by
  let s : ℤ := ⌊β - a⌋
  have hs₁ : (s : ℚ) ≤ β - a := Int.floor_le _
  have hs₂ : β - 1 < a + (s : ℚ) := by
    have h : β - a < (s : ℚ) + 1 := Int.lt_floor_add_one _
    linarith
  have hx : ((β - 1 : ℚ) : WithTop ℚ) < wx (sx s x) := by
    rw [hsx]
    have h := add_le_add_left ha ((s : ℚ) : WithTop ℚ)
    rw [← WithTop.coe_add] at h
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hs₂) h
  have hy := hint _ hx
  rw [hu, hsy] at hy
  let negS : ℚ := -(s : ℚ)
  have hy' := add_le_add_left hy (negS : WithTop ℚ)
  have hcancel : (s : ℚ) + negS = 0 := add_neg_cancel _
  rw [zero_add, add_assoc, ← WithTop.coe_add, hcancel, WithTop.coe_zero, add_zero] at hy'
  exact (WithTop.coe_le_coe.mpr (show a - β ≤ negS by dsimp [negS]; linarith)).trans hy'

/-- Conjugation moves an edge by the difference of the endpoint slopes. -/
theorem transported_block {X Y : Type*}
    (wx : X → WithTop ℚ) (wy : Y → WithTop ℚ)
    (fx : ℤ → X → X) (fy : ℤ → Y → Y) (sy : ℤ → Y → Y) (u : X → Y)
    (slopeX slopeY βx βy : ℚ) (n m : ℤ)
    (hfx : ∀ t x, wx (fx t x) = wx x + ((t : ℚ) * slopeX : ℚ))
    (hfy : ∀ t y, wy (fy t y) = wy y + ((t : ℚ) * slopeY : ℚ))
    (hsy : ∀ t y, wy (sy t y) = wy y + ((t : ℚ) : WithTop ℚ))
    (hu : ∀ (x : X) (a : ℚ), (a : WithTop ℚ) ≤ wx x →
      ((a - βx : ℚ) : WithTop ℚ) ≤ wy (u x))
    (hdir : 0 ≤ (n : ℚ) * (slopeY - slopeX)) (hm : βx + βy - 1 < (m : ℚ))
    (x : X) (hx : 0 ≤ wx x) :
    ((βy - 1 : ℚ) : WithTop ℚ) < wy (sy m (fy n (u (fx (-n) x)))) := by
  have ha : ((-(n : ℚ) * slopeX : ℚ) : WithTop ℚ) ≤ wx (fx (-n) x) := by
    rw [hfx, Int.cast_neg]
    simpa only [zero_add] using add_le_add_left hx ((-(n : ℚ) * slopeX : ℚ) : WithTop ℚ)
  have h := hu _ _ ha
  rw [hsy, hfy]
  apply lt_of_lt_of_le _ (add_le_add_left (add_le_add_left h _) _)
  rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_lt_coe]
  rw [mul_sub] at hdir
  linarith

/-- Every slope edge, transported in the direction of nonnegative drift,
returns the input lattice to itself after multiplication by `p^floor(2B)`.
Selecting the edge set gives the positive, zero, and negative slope parts
of the level module separately. -/
theorem slope_graph_bound {ι : Type*} [DecidableEq ι]
    {X : ι → Type*} [∀ i, AddCommGroup (X i)]
    (L : AddSubgroup (∀ i, X i)) (w : ∀ i, X i → WithTop ℚ)
    (scale frob : ∀ i, ℤ → X i → X i) (slope β : ι → ℚ) (B : ℚ)
    (hs : ∀ i t x, w i (scale i t x) = w i x + ((t : ℚ) : WithTop ℚ))
    (hf : ∀ i t x, w i (frob i t x) = w i x + ((t : ℚ) * slope i : ℚ))
    (hzero : ∀ i, w i 0 = ⊤)
    (hout : ∀ x ∈ L, ∀ i, 0 ≤ w i (x i))
    (hin : ∀ x, (∀ i, ((β i - 1 : ℚ) : WithTop ℚ) < w i (x i)) → x ∈ L)
    (hB : ∀ i, β i ≤ B)
    (u : (∀ i, X i) → (∀ i, X i)) (huL : ∀ x ∈ L, u x ∈ L)
    (hus : ∀ i j t x, u (Pi.single j (scale j t x)) i = scale i t (u (Pi.single j x) i))
    (edges : Finset (ι × ι)) (n : ι → ι → ℤ)
    (hdir : ∀ i j, (i, j) ∈ edges → 0 ≤ (n i j : ℚ) * (slope i - slope j))
    (x : ∀ i, X i) (hx : x ∈ L) :
    (∑ e ∈ edges, Pi.single e.1 (scale e.1 ⌊2 * B⌋
      (frob e.1 (n e.1 e.2) (u (Pi.single e.2 (frob e.2 (-(n e.1 e.2)) (x e.2))) e.1))))
      ∈ L := by
  have single_mem (i : ι) (y : X i)
      (hy : ((β i - 1 : ℚ) : WithTop ℚ) < w i y) : Pi.single i y ∈ L := by
    apply hin
    intro k
    by_cases h : k = i
    · subst k
      simpa using hy
    · rw [Pi.single_eq_of_ne h, hzero]
      exact WithTop.coe_lt_top _
  apply L.sum_mem
  rintro ⟨i, j⟩ he
  apply single_mem
  apply transported_block (w j) (w i) (frob j) (frob i) (scale i)
    (fun y => u (Pi.single j y) i) (slope j) (slope i) (β j) (β i) (n i j) ⌊2 * B⌋
    (hf j) (hf i) (hs i) _ (hdir i j he) _ (x j) (hout x hx j)
  · exact block_lower_bound (w j) (w i) (scale j) (scale i)
      (fun y => u (Pi.single j y) i) (β j) (hs j) (hs i) (hus i j)
      (fun y hy => hout _ (huL _ (single_mem j y hy)) i)
  · have h := Int.lt_floor_add_one (2 * B)
    linarith [hB i, hB j]

end TraversoSlopeGraph
