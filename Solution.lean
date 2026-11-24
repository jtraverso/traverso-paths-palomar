module

public import TraversoSlopeGraph
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Nat.Find
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-!
# The cyclic lattice inclusion as a path of Newton slopes

The vertices of the path are the slopes in increasing order. Each vertex
has a Newton interval and a contact interval of the coefficient valuations.
Cancellation across a short contact interval is excluded by the algebraic
input of Lau–Nicole–Vasiu, Lemma 5.16. The path argument proves the lattice
inclusion of Proposition 5.12 at the level of cyclic valuative coordinates.
-/

open scoped BigOperators

@[expose] public section

namespace TraversoSlopeGraph

/-- Reference affine lines with strictly increasing cuts from `0` to `h`.
The cuts used by the path are indexed by `0, …, r`. -/
structure NewtonPath (r h : ℕ) where
  slope : ℕ → ℚ
  intercept : ℕ → ℚ
  cut : ℕ → ℚ
  first_cut : cut 0 = 0
  last_cut : cut r = h
  cut_lt : ∀ j, j < r → cut j < cut (j + 1)
  slope_lt : ∀ j, j + 1 < r → slope j < slope (j + 1)
  meet : ∀ j, j + 1 < r →
    intercept j + slope j * cut (j + 1) = intercept (j + 1) + slope (j + 1) * cut (j + 1)

def NewtonPath.line {r h : ℕ} (P : NewtonPath r h) (j : ℕ) (t : ℚ) : ℚ :=
  P.intercept j + P.slope j * t

/-- The supporting line of the coefficient cloud and its extreme contacts. -/
structure Contacts {h : ℕ} (slope : ℚ) (v : Fin h → WithTop ℚ) where
  offset : ℚ
  left : Fin h
  right : Fin h
  below : ∀ i, ((offset + slope * (i.val : ℚ) : ℚ) : WithTop ℚ) ≤ v i
  hits_left : ((offset + slope * (left.val : ℚ) : ℚ) : WithTop ℚ) = v left
  hits_right : ((offset + slope * (right.val : ℚ) : ℚ) : WithTop ℚ) = v right
  extremes : ∀ i, ((offset + slope * (i.val : ℚ) : ℚ) : WithTop ℚ) = v i →
    left ≤ i ∧ i ≤ right

/-- A finite coefficient cloud with a nonzero coefficient determines its
supporting line and its leftmost and rightmost contacts. -/
noncomputable def Contacts.ofCoefficients {h : ℕ} (slope : ℚ) (v : Fin h → WithTop ℚ)
    (hv : ∃ i, v i ≠ ⊤) : Contacts slope v := by
  classical
  let weight (i : Fin h) : ℚ := slope * i.val
  let score (i : Fin h) : WithTop ℚ := v i + ((-(weight i) : ℚ) : WithTop ℚ)
  let values : Finset (WithTop ℚ) := Finset.univ.image score
  have mem_values (i : Fin h) : score i ∈ values := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  let i₀ := Classical.choose hv
  have hi₀ : v i₀ ≠ ⊤ := Classical.choose_spec hv
  have hvalues : values.Nonempty := ⟨score i₀, mem_values i₀⟩
  let lo := values.min' hvalues
  have lo_le (i : Fin h) : lo ≤ score i := values.min'_le _ (mem_values i)
  have hlo : lo ≠ ⊤ := by
    have hfinite : score i₀ ≠ ⊤ := by simp [score, hi₀]
    exact ne_top_of_le_ne_top hfinite (lo_le i₀)
  let offset : ℚ := lo.untop hlo
  have hoffset : (offset : WithTop ℚ) = lo := WithTop.coe_untop _ _
  let hit : Finset (Fin h) := Finset.univ.filter (fun i => score i = lo)
  have hhit : hit.Nonempty := by
    have hmem : lo ∈ values := values.min'_mem hvalues
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hmem
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, heq⟩⟩
  have restore (i : Fin h) : score i + (weight i : WithTop ℚ) = v i := by
    change v i + ((-(weight i) : ℚ) : WithTop ℚ) + (weight i : WithTop ℚ) = v i
    rw [add_assoc, ← WithTop.coe_add, neg_add_cancel, WithTop.coe_zero, add_zero]
  have is_contact (i : Fin h) : i ∈ hit ↔ ((offset + weight i : ℚ) : WithTop ℚ) = v i := by
    change i ∈ Finset.univ.filter (fun i => score i = lo) ↔ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [WithTop.coe_add, hoffset, ← restore i]
    constructor
    · intro heq
      rw [heq]
    · intro heq
      refine le_antisymm ?_ (lo_le i)
      apply (WithTop.add_le_add_iff_right (z := (weight i : WithTop ℚ)) WithTop.coe_ne_top).mp
      exact heq.ge
  refine ⟨offset, hit.min' hhit, hit.max' hhit, ?_, ?_, ?_, ?_⟩
  · intro i
    change ((offset + weight i : ℚ) : WithTop ℚ) ≤ v i
    rw [WithTop.coe_add, hoffset, ← restore i]
    exact add_le_add_left (lo_le i) _
  · exact (is_contact _).mp (hit.min'_mem hhit)
  · exact (is_contact _).mp (hit.max'_mem hhit)
  · intro i hi
    have hmem := (is_contact i).mpr hi
    exact ⟨hit.min'_le i hmem, hit.le_max' i hmem⟩

/-- A vertex below its reference line needs a contact interval at least as
wide as its Newton interval. Propagating rightward along a run of such
vertices contradicts the last contact or the first upward crossing. -/
theorem contacts_above_reference {r h : ℕ} (P : NewtonPath r h)
    (v : Fin h → WithTop ℚ) (C : ∀ j : Fin r, Contacts (P.slope j) v) (shift : ℚ)
    (width : ∀ j : Fin r, (C j).offset ≤ P.intercept j - shift →
      P.cut (j.val + 1) - P.cut j ≤ ((C j).right.val : ℚ) - (C j).left.val) :
    ∀ j : Fin r, P.intercept j - shift < (C j).offset := by
  classical
  have adjacent (j : ℕ) (hj : j + 1 < r) :
      ((((C ⟨j, by omega⟩).right.val : ℕ) : ℚ) ≤ ((C ⟨j + 1, hj⟩).left.val : ℚ)) ∧
      (P.intercept j - shift < (C ⟨j, by omega⟩).offset →
        (C ⟨j + 1, hj⟩).offset ≤ P.intercept (j + 1) - shift →
        P.cut (j + 1) ≤ ((C ⟨j + 1, hj⟩).left.val : ℚ)) ∧
      ((C ⟨j, by omega⟩).offset ≤ P.intercept j - shift →
        P.intercept (j + 1) - shift < (C ⟨j + 1, hj⟩).offset →
        ((C ⟨j, by omega⟩).right.val : ℚ) < P.cut (j + 1)) := by
    let a := C ⟨j, by omega⟩
    let b := C ⟨j + 1, hj⟩
    change ((a.right.val : ℚ) ≤ (b.left.val : ℚ)) ∧
      (P.intercept j - shift < a.offset → b.offset ≤ P.intercept (j + 1) - shift →
        P.cut (j + 1) ≤ (b.left.val : ℚ)) ∧
      (a.offset ≤ P.intercept j - shift → P.intercept (j + 1) - shift < b.offset →
        (a.right.val : ℚ) < P.cut (j + 1))
    have atRight := b.below a.right
    have atLeft := a.below b.left
    rw [← a.hits_right, WithTop.coe_le_coe] at atRight
    rw [← b.hits_left, WithTop.coe_le_coe] at atLeft
    have gap := sub_pos.mpr (P.slope_lt j hj)
    have meet := P.meet j hj
    refine ⟨?_, ?_, ?_⟩
    · by_contra! h
      have hp := mul_pos gap (sub_pos.mpr h)
      nlinarith only [hp, atRight, atLeft]
    · intro ha hb
      by_contra! h
      have hp := mul_pos gap (sub_pos.mpr h)
      nlinarith only [hp, meet, atLeft, ha, hb]
    · intro ha hb
      by_contra! h
      have hp := mul_nonneg gap.le (sub_nonneg.mpr h)
      nlinarith only [hp, meet, atRight, ha, hb]
  have reach : ∀ (j : ℕ) (hj : j < r), (C ⟨j, hj⟩).offset ≤ P.intercept j - shift →
      P.cut (j + 1) ≤ ((C ⟨j, hj⟩).right.val : ℚ) := by
    intro j
    induction j with
    | zero =>
        intro hj hb
        have hw := width ⟨0, hj⟩ hb
        have hl : (0 : ℚ) ≤ ((C ⟨0, hj⟩).left.val : ℚ) := by exact_mod_cast Nat.zero_le _
        change P.cut 1 - P.cut 0 ≤ ((C ⟨0, hj⟩).right.val : ℚ) - (C ⟨0, hj⟩).left.val at hw
        linarith [P.first_cut]
    | succ j ih =>
        intro hj hb
        have hadj := adjacent j hj
        have hleft : P.cut (j + 1) ≤ ((C ⟨j + 1, hj⟩).left.val : ℚ) := by
          by_cases hp : (C ⟨j, by omega⟩).offset ≤ P.intercept j - shift
          · exact (ih (by omega) hp).trans hadj.1
          · exact hadj.2.1 (lt_of_not_ge hp) hb
        have hw := width ⟨j + 1, hj⟩ hb
        change P.cut (j + 1 + 1) - P.cut (j + 1) ≤
          ((C ⟨j + 1, hj⟩).right.val : ℚ) - (C ⟨j + 1, hj⟩).left.val at hw
        linarith
  intro j
  by_contra! hj
  let bad (k : ℕ) : Prop := ∃ hk : k < r, (C ⟨k, hk⟩).offset ≤ P.intercept k - shift
  let k := Nat.findGreatest bad (r - 1)
  have hkmax : k ≤ r - 1 := Nat.findGreatest_le _
  have hbad : bad k := Nat.findGreatest_spec (P := bad) (n := r - 1) (m := j.val)
    (by have := j.isLt; omega) ⟨j.isLt, hj⟩
  obtain ⟨hk, hb⟩ := hbad
  have hr := reach k hk hb
  by_cases hn : k + 1 < r
  · have hgood : ¬ bad (k + 1) := Nat.findGreatest_is_greatest (P := bad) (n := r - 1)
      (by change k < k + 1; omega) (by omega)
    have hright := (adjacent k hn).2.2 hb (lt_of_not_ge fun hz => hgood ⟨hn, hz⟩)
    exact (not_lt_of_ge hr) hright
  · have heq : k + 1 = r := by omega
    rw [heq, P.last_cut] at hr
    have hlast : (((C ⟨k, hk⟩).right.val : ℕ) : ℚ) < (h : ℚ) := by exact_mod_cast (C ⟨k, hk⟩).right.isLt
    exact (not_lt_of_ge hr) hlast

/-- The algebraic inputs of the cyclic presentation, including the local
no-cancellation criterion of Lemma 5.16. The integer `threshold` is the
valuation of the change of basis from Laurent powers to the integral basis. -/
structure CyclicCoordinates {r h : ℕ} (P : NewtonPath r h) (c : ℕ)
    {X : Fin r → Type*} [∀ i, AddCommGroup (X i)]
    (L : AddSubgroup (∀ i, X i)) (w : ∀ i, X i → WithTop ℚ) where
  coeff : (∀ i, X i) → Fin h → WithTop ℚ
  discrete : ∀ x i, coeff x i = ⊤ ∨ ∃ n : ℤ, coeff x i = ((n : ℚ) : WithTop ℚ)
  threshold : Fin h → ℤ
  integral : ∀ x, x ∈ L ↔ ∀ i, ((threshold i : ℚ) : WithTop ℚ) ≤ coeff x i
  covered : ∀ i, ∃ j : Fin r, (threshold i : ℚ) ≤ P.line j i.val
  nonzero_coeff : ∀ x, x ≠ 0 → ∃ i, coeff x i ≠ ⊤
  short_exact : ∀ x (j : Fin r) (contact : Contacts (P.slope j) (coeff x)),
    ((contact.right.val : ℚ) - contact.left.val <
      P.cut (j.val + 1) - P.cut j) →
    w j (x j) = ((contact.offset + P.slope j * (c : ℚ) : ℚ) : WithTop ℚ)

/-- The rescaled inclusion `N^{> β-1} ⊆ M` used in `slope_graph_bound`. -/
theorem cyclic_mem {r h c : ℕ} {P : NewtonPath r h}
    {X : Fin r → Type*} [∀ i, AddCommGroup (X i)]
    {L : AddSubgroup (∀ i, X i)} {w : ∀ i, X i → WithTop ℚ}
    (D : CyclicCoordinates P c L w) (x : ∀ i, X i)
    (hx : ∀ j : Fin r, ((P.line j c - 1 : ℚ) : WithTop ℚ) < w j (x j)) : x ∈ L := by
  by_cases hz : x = 0
  · exact hz.symm ▸ L.zero_mem
  let C (j : Fin r) := Contacts.ofCoefficients (P.slope j) (D.coeff x) (D.nonzero_coeff x hz)
  have hwide (j : Fin r) (hb : (C j).offset ≤ P.intercept j - 1) :
      P.cut (j.val + 1) - P.cut j ≤ ((C j).right.val : ℚ) - (C j).left.val := by
    by_contra! hn
    have hw := hx j
    rw [D.short_exact x j (C j) hn, WithTop.coe_lt_coe, NewtonPath.line] at hw
    linarith
  have habove := contacts_above_reference P (D.coeff x) C 1 hwide
  apply (D.integral x).2
  intro i
  obtain ⟨j, hj⟩ := D.covered i
  have hs : (((D.threshold i : ℚ) - 1 : ℚ) : WithTop ℚ) < D.coeff x i := by
    apply lt_of_lt_of_le _ ((C j).below i)
    apply WithTop.coe_lt_coe.mpr
    have h := habove j
    unfold NewtonPath.line at hj
    linarith
  rcases D.discrete x i with htop | ⟨n, hn⟩
  · rw [htop]
    exact le_top
  · rw [hn, WithTop.coe_lt_coe] at hs
    rw [hn, WithTop.coe_le_coe]
    have hcast : ((D.threshold i - 1 : ℤ) : ℚ) < (n : ℚ) := by push_cast; exact hs
    have hint : D.threshold i - 1 < n := by exact_mod_cast hcast
    exact_mod_cast (show D.threshold i ≤ n by omega)

/-- Proposition 5.12 in the cyclic-coordinate model. -/
theorem proposition_5_12_cyclic {r h c : ℕ} {P : NewtonPath r h}
    {X : Fin r → Type*} [∀ i, AddCommGroup (X i)]
    {L : AddSubgroup (∀ i, X i)} {w : ∀ i, X i → WithTop ℚ}
    (D : CyclicCoordinates P c L w) (scale : ∀ i, ℤ → X i → X i)
    (hs : ∀ i t x, w i (scale i t x) = w i x + ((t : ℚ) : WithTop ℚ))
    (hinv : ∀ i x, scale i 1 (scale i (-1) x) = x)
    (x : ∀ i, X i) (hx : ∀ j : Fin r, (P.line j c : WithTop ℚ) < w j (x j)) :
    ∃ y ∈ L, (fun j => scale j 1 (y j)) = x := by
  let y := fun j => scale j (-1) (x j)
  refine ⟨y, cyclic_mem D y ?_, funext fun j => hinv j (x j)⟩
  intro j
  change ((P.line j c - 1 : ℚ) : WithTop ℚ) < w j (scale j (-1) (x j))
  rw [hs]
  have hn : ((-1 : ℤ) : ℚ) = -1 := by norm_num
  rw [hn]
  rw [sub_eq_add_neg, WithTop.coe_add]
  exact WithTop.add_lt_add_right WithTop.coe_ne_top (hx j)

/-- The cyclic-coordinate graph bound with its lattice inclusion proved by
`cyclic_mem`, the rescaled form of Proposition 5.12. -/
theorem cyclic_slope_graph_bound {r h c : ℕ} {P : NewtonPath r h}
    {X : Fin r → Type*} [∀ i, AddCommGroup (X i)]
    {L : AddSubgroup (∀ i, X i)} {w : ∀ i, X i → WithTop ℚ}
    (D : CyclicCoordinates P c L w)
    (scale frob : ∀ i, ℤ → X i → X i) (B : ℚ)
    (hs : ∀ i t x, w i (scale i t x) = w i x + ((t : ℚ) : WithTop ℚ))
    (hf : ∀ i t x, w i (frob i t x) = w i x + ((t : ℚ) * P.slope i : ℚ))
    (hzero : ∀ i, w i 0 = ⊤)
    (hout : ∀ x ∈ L, ∀ i, 0 ≤ w i (x i))
    (hB : ∀ i : Fin r, P.line i c ≤ B)
    (u : (∀ i, X i) → (∀ i, X i)) (huL : ∀ x ∈ L, u x ∈ L)
    (hus : ∀ i j t x, u (Pi.single j (scale j t x)) i = scale i t (u (Pi.single j x) i))
    (edges : Finset (Fin r × Fin r)) (n : Fin r → Fin r → ℤ)
    (hdir : ∀ i j, (i, j) ∈ edges → 0 ≤ (n i j : ℚ) * (P.slope i - P.slope j))
    (x : ∀ i, X i) (hx : x ∈ L) :
    (∑ e ∈ edges, Pi.single e.1 (scale e.1 ⌊2 * B⌋
      (frob e.1 (n e.1 e.2) (u (Pi.single e.2 (frob e.2 (-(n e.1 e.2)) (x e.2))) e.1))))
      ∈ L :=
  slope_graph_bound L w scale frob (fun i => P.slope i) (fun i => P.line i c) B
    hs hf hzero hout (cyclic_mem D) hB u huL hus edges n hdir x hx

/-- An affine support line below the endpoints of the polygon is below
the chord at the codimension. -/
theorem support_line_le_dimension {r c d : ℕ} (P : NewtonPath r (c + d))
    (hpos : 0 < c + d) (j : Fin r)
    (hleft : P.line j 0 ≤ 0) (hright : P.line j ((c : ℚ) + d) ≤ d) :
    P.line j c ≤ (c : ℚ) * d / ((c : ℚ) + d) := by
  have hh : (0 : ℚ) < (c : ℚ) + d := by exact_mod_cast hpos
  apply (le_div_iff₀ hh).2
  calc
    P.line j c * ((c : ℚ) + d) = (d : ℚ) * P.line j 0 + (c : ℚ) * P.line j ((c : ℚ) + d) := by
      unfold NewtonPath.line
      ring
    _ ≤ (d : ℚ) * 0 + (c : ℚ) * d :=
      add_le_add (mul_le_mul_of_nonneg_left hleft (by positivity))
        (mul_le_mul_of_nonneg_left hright (by positivity))
    _ = (c : ℚ) * d := by simp

/-- The assembled graph bound with the dimension and codimension exponent. -/
theorem cyclic_slope_graph_dimension_bound {r c d : ℕ} {P : NewtonPath r (c + d)}
    {X : Fin r → Type*} [∀ i, AddCommGroup (X i)]
    {L : AddSubgroup (∀ i, X i)} {w : ∀ i, X i → WithTop ℚ}
    (D : CyclicCoordinates P c L w)
    (scale frob : ∀ i, ℤ → X i → X i)
    (hs : ∀ i t x, w i (scale i t x) = w i x + ((t : ℚ) : WithTop ℚ))
    (hf : ∀ i t x, w i (frob i t x) = w i x + ((t : ℚ) * P.slope i : ℚ))
    (hzero : ∀ i, w i 0 = ⊤)
    (hout : ∀ x ∈ L, ∀ i, 0 ≤ w i (x i))
    (hpos : 0 < c + d) (hleft : ∀ i : Fin r, P.line i 0 ≤ 0)
    (hright : ∀ i : Fin r, P.line i ((c : ℚ) + d) ≤ d)
    (u : (∀ i, X i) → (∀ i, X i)) (huL : ∀ x ∈ L, u x ∈ L)
    (hus : ∀ i j t x, u (Pi.single j (scale j t x)) i = scale i t (u (Pi.single j x) i))
    (edges : Finset (Fin r × Fin r)) (n : Fin r → Fin r → ℤ)
    (hdir : ∀ i j, (i, j) ∈ edges → 0 ≤ (n i j : ℚ) * (P.slope i - P.slope j))
    (x : ∀ i, X i) (hx : x ∈ L) :
    (∑ e ∈ edges, Pi.single e.1 (scale e.1 ⌊2 * ((c : ℚ) * d / ((c : ℚ) + d))⌋
      (frob e.1 (n e.1 e.2) (u (Pi.single e.2 (frob e.2 (-(n e.1 e.2)) (x e.2))) e.1))))
      ∈ L :=
  cyclic_slope_graph_bound D scale frob ((c : ℚ) * d / ((c : ℚ) + d)) hs hf hzero hout
    (fun i => support_line_le_dimension P hpos i (hleft i) (hright i)) u huL hus edges n hdir x hx

end TraversoSlopeGraph
