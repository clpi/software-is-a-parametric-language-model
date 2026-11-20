/-
  The parametric rewritable language model: the proved core.

  The model, from the directive of 2026-11-20. A language
  model whose behavior is a totally deterministic function of
  the content and a parameter assignment whose every component
  is named and legible: a determination route, named objective
  axes with weights, a token overlay of keyed rational
  multipliers, an acceptability threshold, an enumeration
  bound, and a tiebreak order. This module proves the load
  bearing properties of that construction over finite tables:
  the certified answer is unique and optimal over the
  enumerated complete set; certification is sound under its
  stated coverage premise and is refused while an unresolved
  bound exceeds the best complete score; the overlay algebra
  is exact (identity, inverse round trip, cone invariance);
  and a reweighting touches only derivations in its premise
  cone, so reused values outside the cone equal full
  recomputation there.

  Scores on the deterministic path are products of rational
  token weights. A rational is carried as a numerator and a
  denominator in lowest terms or not; equality and order are
  by cross multiplication, so no normal form is ever needed.
-/

namespace Prlm

/-- A token. -/
abbrev Tok := Nat

/-- A rational weight as a numerator and a denominator.
    The denominator is positive wherever the weight is used;
    that side condition rides on the theorems, not the type,
    so cross multiplication never needs a normal form. -/
abbrev Frac := Nat × Nat

/-- Fraction equality: cross multiplied equality. -/
def feq (a b : Frac) : Prop := a.1 * b.2 = b.1 * a.2

/-- Fraction order: cross multiplied order. -/
def fle (a b : Frac) : Prop := a.1 * b.2 ≤ b.1 * a.2

/-- Fraction multiplication, componentwise. -/
def fmul (a b : Frac) : Frac := (a.1 * b.1, a.2 * b.2)

/-- The unit fraction. -/
def fone : Frac := (1, 1)

/-- The inverse fraction: numerator and denominator swapped. -/
def finv (a : Frac) : Frac := (a.2, a.1)

theorem feqrefl (a : Frac) : feq a a := rfl

theorem feqsymm {a b : Frac} (h : feq a b) : feq b a := h.symm

/-- Cross multiplied equality is transitive wherever the
    middle denominator is positive. The two cases are the
    middle numerator vanishing, which forces both ends to
    vanish, and the positive case, which cancels the middle
    denominator from a product inequality turned equality. -/
theorem feqtrans {a b c : Frac} (hb : 0 < b.2) (h1 : feq a b) (h2 : feq b c) :
    feq a c := by
  unfold feq at *
  rcases Nat.eq_zero_or_pos b.1 with hb1 | _
  · have ha : a.1 = 0 := by
      have hz : a.1 * b.2 = 0 := by rw [hb1] at h1; simpa using h1
      rcases Nat.mul_eq_zero.mp hz with h | h
      · exact h
      · omega
    have hc : c.1 = 0 := by
      have hz : c.1 * b.2 = 0 := by rw [hb1] at h2; simpa using h2.symm
      rcases Nat.mul_eq_zero.mp hz with h | h
      · exact h
      · omega
    rw [ha, hc]; simp
  · have key : a.1 * c.2 * b.2 = c.1 * a.2 * b.2 := by
      calc a.1 * c.2 * b.2 = (a.1 * b.2) * c.2 := by ac_rfl
        _ = (b.1 * a.2) * c.2 := by rw [h1]
        _ = (b.1 * c.2) * a.2 := by ac_rfl
        _ = (c.1 * b.2) * a.2 := by rw [h2]
        _ = c.1 * a.2 * b.2 := by ac_rfl
    exact Nat.eq_of_mul_eq_mul_right hb key

/-- Cross multiplied order is reflexive. -/
theorem flerefl (a : Frac) : fle a a := Nat.le_refl _

/-- Cross multiplied order is transitive wherever the middle
    denominator is positive: multiply the two hypotheses by
    the far denominators, chain them at the shared middle
    product, and cancel the middle denominator. -/
theorem fletrans {a b c : Frac} (hb : 0 < b.2) (h1 : fle a b) (h2 : fle b c) :
    fle a c := by
  unfold fle at *
  rcases Nat.eq_zero_or_pos b.1 with hb1 | _
  · have ha : a.1 = 0 := by
      have h : a.1 * b.2 ≤ 0 := by rw [hb1] at h1; simpa using h1
      have hz : a.1 * b.2 = 0 := Nat.eq_zero_of_le_zero h
      rcases Nat.mul_eq_zero.mp hz with h0 | h0
      · exact h0
      · omega
    rw [ha]; simp
  · have key : a.1 * c.2 * b.2 ≤ c.1 * a.2 * b.2 := by
      calc a.1 * c.2 * b.2 = (a.1 * b.2) * c.2 := by ac_rfl
        _ ≤ (b.1 * a.2) * c.2 := Nat.mul_le_mul_right _ h1
        _ = (b.1 * c.2) * a.2 := by ac_rfl
        _ ≤ (c.1 * b.2) * a.2 := Nat.mul_le_mul_right _ h2
        _ = c.1 * a.2 * b.2 := by ac_rfl
    exact Nat.le_of_mul_le_mul_right key hb

/-- Equal fractions stand in the order both ways. -/
theorem fleofeq {a b : Frac} (h : feq a b) : fle a b := Nat.le_of_eq h

/-- Multiplication respects fraction equality in both
    arguments at once. -/
theorem fmuleq {a a' b b' : Frac} (ha : feq a a') (hb : feq b b') :
    feq (fmul a b) (fmul a' b') := by
  unfold feq fmul at *
  calc (a.1 * b.1) * (a'.2 * b'.2) = (a.1 * a'.2) * (b.1 * b'.2) := by ac_rfl
    _ = (a'.1 * a.2) * (b'.1 * b.2) := by rw [ha, hb]
    _ = (a'.1 * b'.1) * (a.2 * b.2) := by ac_rfl

/-- The unit fraction is a left and right identity up to
    fraction equality; in fact the products are equal as
    pairs after one simplification each. -/
theorem fmulone (a : Frac) : feq (fmul a fone) a := by
  unfold feq fmul fone; simp [Nat.mul_comm]

theorem fonemul (a : Frac) : feq (fmul fone a) a := by
  unfold feq fmul fone; simp [Nat.mul_comm]

/-- A fraction times its inverse is the unit, wherever the
    numerator is positive: the cross product is one product
    of the two components read in the two orders. -/
theorem fmulinv (a : Frac) : feq (fmul a (finv a)) fone := by
  unfold feq fmul finv fone
  calc (a.1 * a.2) * 1 = a.1 * a.2 := Nat.mul_one _
    _ = 1 * (a.2 * a.1) := by rw [Nat.mul_comm a.2 a.1]; simp

/-- Multiplication on the right preserves the order:
    scaling both sides of an order by one fraction keeps it. -/
theorem flemul {a b c : Frac} (h : fle a b) : fle (fmul a c) (fmul b c) := by
  unfold fle fmul at *
  calc (a.1 * c.1) * (b.2 * c.2) = (a.1 * b.2) * (c.1 * c.2) := by ac_rfl
    _ ≤ (b.1 * a.2) * (c.1 * c.2) := Nat.mul_le_mul_right _ h
    _ = (b.1 * c.1) * (a.2 * c.2) := by ac_rfl

end Prlm

/- Selection. The decoder's answer is the champion of a
   candidate list under a score and an order: scan the list,
   keep the head against the champion of the tail, and on a
   tie keep the earlier element. The tiebreak is therefore
   the enumeration order itself, and it is a parameter of the
   model, never an unstated convention. The lemmas below are
   proved for any score type carrying a reflexive, transitive,
   total order; they are instantiated at natural scores for
   the plain path and at fraction scores under an overlay. -/

namespace Sel

variable {α S : Type} (le : S → S → Prop) [DecidableRel le] (score : α → S)

/-- Keep the earlier of two candidates unless the later one
    is strictly ahead: the later wins exactly when the earlier
    does not stand in the order over it. -/
def pick (a b : α) : α := if le (score b) (score a) then a else b

/-- The champion of a list: none on the empty list, else the
    first element attaining the maximum score. -/
def sel : List α → Option α
  | [] => none
  | x :: xs => some (match sel xs with
      | none => x
      | some y => pick le score x y)

theorem selnone {cs : List α} : sel le score cs = none ↔ cs = [] := by
  cases cs with
  | nil => simp [sel]
  | cons x xs =>
    simp only [sel]
    cases sel le score xs <;> simp

theorem selmem {cs : List α} {s : α} (h : sel le score cs = some s) :
    s ∈ cs := by
  induction cs generalizing s with
  | nil => simp [sel] at h
  | cons x xs ih =>
    simp only [sel] at h
    cases hxs : sel le score xs with
    | none =>
      rw [hxs] at h; simp only [Option.some.injEq] at h; subst h
      exact List.mem_cons.mpr (Or.inl rfl)
    | some y =>
      rw [hxs] at h
      have hy : y ∈ xs := ih hxs
      by_cases hc : le (score y) (score x)
      · simp only [pick, hc, if_true, Option.some.injEq] at h; subst h
        exact List.mem_cons.mpr (Or.inl rfl)
      · simp only [pick, hc, if_false, Option.some.injEq] at h; subst h
        exact List.mem_cons_of_mem x hy

/-- The champion attains the maximum: every candidate in the
    list stands in the order under the champion's score. -/
theorem selmax (hrefl : ∀ s : S, le s s)
    (htrans : ∀ {a b c : S}, le a b → le b c → le a c)
    (htotal : ∀ a b : S, le a b ∨ le b a)
    {cs : List α} {s : α} (h : sel le score cs = some s) :
    ∀ c ∈ cs, le (score c) (score s) := by
  induction cs generalizing s with
  | nil => simp [sel] at h
  | cons x xs ih =>
    simp only [sel] at h
    cases hxs : sel le score xs with
    | none =>
      rw [hxs] at h; simp only [Option.some.injEq] at h; subst h
      have hxe : xs = [] := (selnone le score).mp hxs
      subst hxe; intro c hc; simp at hc; subst hc; exact hrefl _
    | some y =>
      rw [hxs] at h
      have hymax : ∀ c ∈ xs, le (score c) (score y) := ih hxs
      by_cases hc : le (score y) (score x)
      · simp only [pick, hc, if_true, Option.some.injEq] at h; subst h
        intro c hcm
        rcases List.mem_cons.mp hcm with rfl | hcx
        · exact hrefl _
        · exact htrans (hymax c hcx) hc
      · simp only [pick, hc, if_false, Option.some.injEq] at h; subst h
        intro c hcm
        rcases List.mem_cons.mp hcm with rfl | hcx
        · exact (htotal _ _).elim id (fun hle => absurd hle hc)
        · exact hymax c hcx

/-- The champion is the first maximum: no element before it
    in the list stands over it in the order. Stated over
    duplicate free lists, where a split at the champion's
    value names its one occurrence. -/
theorem selfirst
    {cs : List α} (hnd : cs.Nodup) {s : α} (h : sel le score cs = some s) :
    ∀ l₁ l₂, cs = l₁ ++ s :: l₂ → ∀ c ∈ l₁, ¬ le (score s) (score c) := by
  induction cs with
  | nil => simp [sel] at h
  | cons x xs ih =>
    simp only [sel] at h
    cases hxs : sel le score xs with
    | none =>
      rw [hxs] at h; simp only [Option.some.injEq] at h; subst h
      have hxe : xs = [] := (selnone le score).mp hxs
      subst hxe
      intro l₁ l₂ hsplit c hc
      have hl1 : l₁ = [] := by
        cases l₁ with
        | nil => rfl
        | cons a as =>
          exfalso
          rw [List.cons_append] at hsplit
          have h2 := (List.cons.inj hsplit).2
          cases as with
          | nil => simp at h2
          | cons b bs => simp at h2
      subst hl1; simp at hc
    | some y =>
      rw [hxs] at h
      have hy : y ∈ xs := selmem le score hxs
      have hndxs : xs.Nodup := (List.nodup_cons.mp hnd).2
      by_cases hc : le (score y) (score x)
      · simp only [pick, hc, if_true, Option.some.injEq] at h; subst h
        intro l₁ l₂ hsplit c hcm
        have hxnot : x ∉ xs := (List.nodup_cons.mp hnd).1
        have hl1 : l₁ = [] := by
          cases l₁ with
          | nil => rfl
          | cons a as =>
            exfalso
            have h2 : x :: xs = a :: (as ++ x :: l₂) := hsplit
            have ha : x = a := (List.cons.inj h2).1
            have h3 : xs = as ++ x :: l₂ := (List.cons.inj h2).2
            subst ha
            have hmem : x ∈ xs := by
              rw [h3]
              exact List.mem_append_right as (List.mem_cons.mpr (Or.inl rfl))
            exact hxnot hmem
        subst hl1; simp at hcm
      · simp only [pick, hc, if_false, Option.some.injEq] at h; subst h
        intro l₁ l₂ hsplit c hcm
        cases l₁ with
        | nil => simp at hcm
        | cons a as =>
          have h2 : x :: xs = a :: (as ++ y :: l₂) := hsplit
          have ha : x = a := (List.cons.inj h2).1
          have h3 : xs = as ++ y :: l₂ := (List.cons.inj h2).2
          subst ha
          rcases List.mem_cons.mp hcm with rfl | hcas
          · exact hc
          · exact ih hndxs hxs as l₂ h3 c hcas

/-- The selection specification: membership, maximality, and
    firstness. The champion satisfies it, and on a duplicate
    free list it is the only element that does — this is the
    determinism of the model stated as mathematics: the
    parameters (score, order, enumeration) determine the
    answer uniquely. -/
def spec (cs : List α) (s : α) : Prop :=
  s ∈ cs ∧ (∀ c ∈ cs, le (score c) (score s)) ∧
  (∀ l₁ l₂, cs = l₁ ++ s :: l₂ → ∀ c ∈ l₁, ¬ le (score s) (score c))

theorem sel_spec (hrefl : ∀ s : S, le s s)
    (htrans : ∀ {a b c : S}, le a b → le b c → le a c)
    (htotal : ∀ a b : S, le a b ∨ le b a)
    {cs : List α} (hnd : cs.Nodup) {s : α} (h : sel le score cs = some s) :
    spec le score cs s :=
  ⟨selmem le score h, selmax le score hrefl htrans htotal h,
   selfirst le score hnd h⟩

/-- A membership split: any element of a list divides it
    into a part before and a part after its occurrence. -/
theorem memsplit {a : α} {cs : List α} (h : a ∈ cs) :
    ∃ l₁ l₂, cs = l₁ ++ a :: l₂ := by
  induction cs with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | hm
    · exact ⟨[], xs, rfl⟩
    · obtain ⟨l₁, l₂, hsplit⟩ := ih hm
      exact ⟨x :: l₁, l₂, by simp [hsplit]⟩

set_option linter.unusedSectionVars false in
theorem spec_unique {cs : List α} {s₁ s₂ : α}
    (h1 : spec le score cs s₁) (h2 : spec le score cs s₂) : s₁ = s₂ := by
  refine Classical.byContradiction (fun hne => ?_)
  obtain ⟨hmem1, hmax1, hfirst1⟩ := h1
  obtain ⟨hmem2, hmax2, hfirst2⟩ := h2
  obtain ⟨l₁, l₂, hsplit⟩ := memsplit hmem1
  have h2cases : s₂ ∈ l₁ ∨ s₂ ∈ l₂ := by
    have hm : s₂ ∈ l₁ ++ s₁ :: l₂ := hsplit ▸ hmem2
    rcases List.mem_append.mp hm with h | h
    · exact Or.inl h
    · rcases List.mem_cons.mp h with rfl | h
      · exact absurd rfl hne
      · exact Or.inr h
  rcases h2cases with h2in | h2in
  · exact hfirst1 l₁ l₂ hsplit s₂ h2in (hmax2 s₁ hmem1)
  · obtain ⟨u, v, hsplit2⟩ := memsplit h2in
    have hcs : cs = (l₁ ++ s₁ :: u) ++ s₂ :: v := by
      rw [hsplit, hsplit2]; simp [List.append_assoc]
    have h1in : s₁ ∈ l₁ ++ s₁ :: u :=
      List.mem_append_right l₁ (List.mem_cons.mpr (Or.inl rfl))
    exact hfirst2 (l₁ ++ s₁ :: u) v hcs s₁ h1in (hmax1 s₂ hmem2)

end Sel


/- The table and the deterministic path. Rows are recorded
   next token weights at a prefix; a missing row is a state,
   never a zero. The decoder enumerates the complete answers
   within the bound and selects the champion under the path
   score, so its output satisfies the selection specification
   of the previous section: membership, maximality, and
   firstness — and by uniqueness there, the output is the one
   answer the parameters determine. -/

namespace Prlm

/-- A row: recorded next token weights at one prefix. -/
abbrev Row := List (Tok × Nat)

/-- A table: a row where recorded, none where missing. -/
abbrev Table := List Tok → Option Row

/-- The recorded weight of a token at a prefix, zero where
    the row is missing or the token is absent from it. The
    zero is a scoring convention inside the enumerated set;
    the certification layer below never reads a missing row
    as zero — it reads it as an unresolved bound. -/
def weight (t : Table) (pre : List Tok) (x : Tok) : Nat :=
  match t pre with
  | none => 0
  | some row => match row.find? (fun e => e.1 = x) with
    | some e => e.2
    | none => 0

/-- The path score of a sequence read from a starting
    prefix: the product of the recorded weights along it. -/
def pscore (t : Table) (pre : List Tok) : List Tok → Nat
  | [] => 1
  | x :: xs => weight t pre x * pscore t (pre ++ [x]) xs

/-- The complete answers within a remaining depth, read from
    a starting prefix: the prefix itself where the
    completeness rule accepts it, else the union over its
    recorded row of the completions below each next token.
    A missing row contributes nothing here; it contributes
    its bound to the frontier list below. -/
def completes (t : Table) (done : List Tok → Bool) (pre : List Tok) :
    Nat → List (List Tok)
  | 0 => if done pre then [pre] else []
  | n + 1 => if done pre then [pre] else
      match t pre with
      | none => []
      | some row => row.flatMap (fun e => completes t done (pre ++ [e.1]) n)

/-- The frontier bounds within a remaining depth: the path
    scores of the prefixes the enumeration reaches but does
    not complete — depth exhausted, or row missing. These are
    the upper bounds of the unresolved branches. -/
def bounds (t : Table) (done : List Tok → Bool) (pre : List Tok) :
    Nat → List Nat
  | 0 => if done pre then [] else [pscore t [] pre]
  | n + 1 => if done pre then [] else
      match t pre with
      | none => [pscore t [] pre]
      | some row => row.flatMap (fun e => bounds t done (pre ++ [e.1]) n)

/-- The feed forward deterministic path: the champion of the
    enumerated complete answers under the path score, with
    the enumeration order as the tiebreak. -/
def decode (t : Table) (done : List Tok → Bool) (n : Nat) :
    Option (List Tok) :=
  Sel.sel (· ≤ ·) (pscore t []) (completes t done [] n)

theorem appendinj {pre a b : List Tok} (h : pre ++ a = pre ++ b) :
    a = b := by
  induction pre with
  | nil => exact h
  | cons x xs ih => exact ih (List.cons.inj h).2

/-- Every enumerated completion extends its starting prefix. -/
theorem completes_extends {t : Table} {done : List Tok → Bool} :
    ∀ {n pre s}, s ∈ completes t done pre n → pre <+: s := by
  intro n
  induction n with
  | zero =>
    intro pre s hs
    by_cases hd : done pre
    · have hs' : s = pre := by simpa [completes, hd] using hs
      rw [hs']; exact ⟨[], List.append_nil pre⟩
    · simp [completes, hd] at hs
  | succ n ih =>
    intro pre s hs
    by_cases hd : done pre
    · have hs' : s = pre := by simpa [completes, hd] using hs
      rw [hs']; exact ⟨[], List.append_nil pre⟩
    · have hs2 : s ∈ (match t pre with
        | none => ([] : List (List Tok))
        | some row => row.flatMap (fun e : Tok × Nat =>
            completes t done (pre ++ [e.1]) n)) := by
        simpa [completes, hd] using hs
      cases hrow : t pre with
      | none => simp [hrow] at hs2
      | some row =>
        rw [hrow] at hs2
        obtain ⟨e, _, hs3⟩ := List.mem_flatMap.mp hs2
        obtain ⟨u, hu⟩ := ih hs3
        exact ⟨[e.1] ++ u, by rw [← List.append_assoc]; exact hu⟩

/-- Row well formedness, the formal form of the
    specification's row condition: a row is a finite function
    graph — no entry repeated, and no token carried twice. -/
def Rowok (row : Row) : Prop :=
  row.Nodup ∧ ∀ e₁ ∈ row, ∀ e₂ ∈ row, e₁.1 = e₂.1 → e₁ = e₂

/-- A flat map over a list is pairwise distinct when each
    part is, and parts over different entries disagree
    everywhere. Proved directly: the core library carries no
    flat map distinctness lemma under that name. -/
theorem pairwise_flatmap {f : Tok × Nat → List (List Tok)} {row : Row}
    (hf : ∀ e ∈ row, (f e).Pairwise (· ≠ ·))
    (hd : ∀ e₁ ∈ row, ∀ e₂ ∈ row, e₁ ≠ e₂ →
      ∀ a ∈ f e₁, ∀ b ∈ f e₂, a ≠ b)
    (hnd : row.Nodup) :
    (row.flatMap f).Pairwise (· ≠ ·) := by
  induction row with
  | nil => exact List.Pairwise.nil
  | cons e es ih =>
    rw [List.flatMap_cons, List.pairwise_append]
    have hnd' := (List.nodup_cons.mp hnd).2
    have hnot : e ∉ es := (List.nodup_cons.mp hnd).1
    refine ⟨hf e (List.mem_cons.mpr (Or.inl rfl)),
      ih (fun e' he' => hf e' (List.mem_cons_of_mem _ he'))
        (fun e₁ h₁ e₂ h₂ hne => hd e₁ (List.mem_cons_of_mem _ h₁)
          e₂ (List.mem_cons_of_mem _ h₂) hne) hnd', ?_⟩
    intro a ha b hb
    obtain ⟨e', he', hb'⟩ := List.mem_flatMap.mp hb
    have hne : e ≠ e' := by
      intro hcontra
      subst hcontra; exact hnot he'
    exact hd e (List.mem_cons.mpr (Or.inl rfl)) e'
      (List.mem_cons_of_mem _ he') hne a ha b hb'

/-- The enumerated completions are duplicate free wherever
    every recorded row is well formed: two different next
    tokens lead to completions that differ at that token, so
    the parts of the enumeration are disjoint. -/
theorem completes_nodup {t : Table} {done : List Tok → Bool}
    (hrow : ∀ pre row, t pre = some row → Rowok row) :
    ∀ {n pre}, (completes t done pre n).Nodup := by
  intro n
  induction n with
  | zero =>
    intro pre
    by_cases hd : done pre
    · simp [completes, hd]
    · simp [completes, hd]
  | succ n ih =>
    intro pre
    by_cases hd : done pre
    · simp [completes, hd]
    · have hdf : done pre = false := by
        cases hdp : done pre with
        | false => rfl
        | true => exact (hd hdp).elim
      cases hrow' : t pre with
      | none => simp [completes, hdf, hrow']
      | some row =>
        have hok := hrow pre row hrow'
        simp only [completes, hdf, hrow']
        exact pairwise_flatmap (fun e _ => ih)
          (fun e₁ he₁ e₂ he₂ hne a ha b hb hab => by
            obtain ⟨u, hu⟩ := completes_extends ha
            obtain ⟨v, hv⟩ := completes_extends hb
            rw [hab] at hu
            have hpath : [e₁.1] ++ u = [e₂.1] ++ v :=
              appendinj (a := [e₁.1] ++ u) (b := [e₂.1] ++ v) (by
                calc pre ++ ([e₁.1] ++ u) = (pre ++ [e₁.1]) ++ u := by
                      rw [← List.append_assoc]
                  _ = (pre ++ [e₂.1]) ++ v := by rw [hu, hv]
                  _ = pre ++ ([e₂.1] ++ v) := by rw [List.append_assoc])
            have htok : e₁.1 ≠ e₂.1 := by
              intro hcontra
              exact hne (hok.2 e₁ he₁ e₂ he₂ hcontra)
            exact htok (List.cons.inj hpath).1) hok.1

/-- The decoder's output satisfies the selection
    specification over the enumerated complete set. -/
theorem decode_spec {t : Table} {done : List Tok → Bool}
    (hrow : ∀ pre row, t pre = some row → Rowok row)
    {n : Nat} {s : List Tok} (h : decode t done n = some s) :
    Sel.spec (· ≤ ·) (pscore t []) (completes t done [] n) s :=
  Sel.sel_spec (· ≤ ·) (pscore t []) (fun _ => Nat.le_refl _)
    (fun h1 h2 => Nat.le_trans h1 h2) (fun a b => Nat.le_total a b)
    (completes_nodup hrow) h

/-- Determinism, stated as mathematics: any answer meeting
    the selection specification over the enumerated set is
    the decoder's output. The content, the table, and the
    parameters — score, order, bound, tiebreak — determine
    the action stream uniquely. -/
theorem decode_determined {t : Table} {done : List Tok → Bool}
    (hrow : ∀ pre row, t pre = some row → Rowok row)
    {n : Nat} {s : List Tok}
    (hs : Sel.spec (· ≤ ·) (pscore t []) (completes t done [] n) s)
    (hne : completes t done [] n ≠ []) :
    decode t done n = some s := by
  cases hsel : Sel.sel (· ≤ ·) (pscore t []) (completes t done [] n) with
  | none =>
    have hempty : completes t done [] n = [] := (Sel.selnone _ _).mp hsel
    exact absurd hempty hne
  | some s' =>
    have hspec := decode_spec hrow hsel
    have heq := Sel.spec_unique (· ≤ ·) (pscore t []) hspec hs
    rw [heq] at hsel; exact hsel

/-- The certification face of the stop rule: a best complete
    score is certified against a frontier bound list when
    every bound stands under it. -/
def certified (best : Nat) (bs : List Nat) : Prop :=
  ∀ b ∈ bs, b ≤ best

/-- Certification soundness: under the coverage premise —
    every deeper complete score either stands under the best
    or under one of the frontier bounds — a certified best is
    an upper bound on every deeper complete score. The
    coverage premise is where the model's work is: a
    completion never exceeds its own prefix's bound, because
    probability factors are at most one (premise P-bound in
    the program census, with its falsification route). -/
theorem cert_sound {best : Nat} {bs deeper : List Nat}
    (hcert : certified best bs)
    (hcover : ∀ s ∈ deeper, s ≤ best ∨ ∃ b ∈ bs, s ≤ b) :
    ∀ s ∈ deeper, s ≤ best := by
  intro s hs
  rcases hcover s hs with h | ⟨b, hb, hsb⟩
  · exact h
  · exact Nat.le_trans hsb (hcert b hb)

/-- The blocking direction: while one frontier bound exceeds
    the best complete score, certification is refused. An
    unresolved branch is never silently dropped and never
    read as beaten. -/
theorem cert_blocked {best b : Nat} {bs : List Nat}
    (hb : b ∈ bs) (hgt : best < b) : ¬ certified best bs :=
  fun hcert => Nat.not_le_of_gt hgt (hcert b hb)

end Prlm

/- The overlay: route two of the reweighting discipline.
   An overlay adjusts recorded weights by named rational
   multipliers at named keys; removing it restores the
   original weights exactly; and a path that never touches an
   edited key scores exactly as it scored before. Fraction
   weights throughout: the product along a path is a product
   of fractions, and every equality below is fraction
   equality by cross multiplication. -/

namespace Prlm

/-- A row of fraction weights. -/
abbrev FRow := List (Tok × Frac)

/-- A table of fraction weights. -/
abbrev FTable := List Tok → Option FRow

/-- The recorded fraction weight of a token at a prefix; the
    zero fraction where the row is missing or the token is
    absent from it. -/
def fweight (t : FTable) (pre : List Tok) (x : Tok) : Frac :=
  match t pre with
  | none => (0, 1)
  | some row => match row.find? (fun e => e.1 = x) with
    | some e => e.2
    | none => (0, 1)

/-- The path score under a weight function: the product of
    the weights along the sequence, in order. -/
def wscore (w : List Tok → Tok → Frac) (pre : List Tok) :
    List Tok → Frac
  | [] => fone
  | x :: xs => fmul (w pre x) (wscore w (pre ++ [x]) xs)

/-- An edit: a key — a prefix and a token — and the
    multiplier recorded for it. -/
abbrev Edit := List Tok × Tok × Frac

/-- An overlay: a list of edits, read by first match at a
    key. The edit operation of the specification refuses a
    second edit at a key that carries one; first match is the
    graceful form of that refusal, and every theorem below is
    stated for the first match reading. -/
abbrev Overlay := List Edit

/-- The multiplier an overlay applies at a key: the first
    matching edit's multiplier, the unit where none matches. -/
def multat : Overlay → List Tok → Tok → Frac
  | [], _, _ => fone
  | e :: es, pre, x =>
    if e.1 = pre ∧ e.2.1 = x then e.2.2 else multat es pre x

/-- The inverse overlay: every multiplier inverted, order
    kept, so the first match at a key in the inverse is the
    inverse of the first match in the original. -/
def invov (o : Overlay) : Overlay :=
  o.map (fun e => (e.1, e.2.1, finv e.2.2))

/-- The adjusted weight function: the recorded weight times
    the overlay's multiplier at each key. -/
def aweight (t : FTable) (o : Overlay) (pre : List Tok)
    (x : Tok) : Frac :=
  fmul (fweight t pre x) (multat o pre x)

/-- Fraction multiplication is associative up to fraction
    equality: the two cross products are one product of six
    factors read in two associations. -/
theorem fmulassoc (a b c : Frac) :
    feq (fmul (fmul a b) c) (fmul a (fmul b c)) := by
  show ((a.1 * b.1) * c.1) * (a.2 * (b.2 * c.2))
    = (a.1 * (b.1 * c.1)) * ((a.2 * b.2) * c.2)
  ac_rfl

/-- The denominator of a product is the product of the
    denominators, definitionally; positivity follows. -/
theorem fmul_pos2 {a b : Frac} (ha : 0 < a.2) (hb : 0 < b.2) :
    0 < (fmul a b).2 :=
  Nat.mul_pos ha hb

/-- The inverse overlay's multiplier at a key is the inverse
    of the overlay's multiplier there. -/
theorem multat_inv (o : Overlay) (pre : List Tok) (x : Tok) :
    feq (multat (invov o) pre x) (finv (multat o pre x)) := by
  induction o with
  | nil => exact feqrefl _
  | cons e es ih =>
    by_cases hc : e.1 = pre ∧ e.2.1 = x
    · have h1 : multat ((e.1, e.2.1, finv e.2.2) :: invov es) pre x
          = finv e.2.2 := by
        simp only [multat, if_pos hc]
      have h2 : multat (e :: es) pre x = e.2.2 := by
        simp only [multat, if_pos hc]
      have h3 : invov (e :: es)
          = (e.1, e.2.1, finv e.2.2) :: invov es := rfl
      rw [h3, h1, h2]; exact feqrefl _
    · have h1 : multat ((e.1, e.2.1, finv e.2.2) :: invov es) pre x
          = multat (invov es) pre x := by
        simp only [multat, if_neg hc]
      have h2 : multat (e :: es) pre x = multat es pre x := by
        simp only [multat, if_neg hc]
      have h3 : invov (e :: es)
          = (e.1, e.2.1, finv e.2.2) :: invov es := rfl
      rw [h3, h1, h2]; exact ih

/-- The multiplier at a key is a positive fraction wherever
    every recorded multiplier is one. -/
theorem multat_pos {o : Overlay}
    (hm : ∀ e ∈ o, 0 < e.2.2.1 ∧ 0 < e.2.2.2) :
    ∀ pre x, 0 < (multat o pre x).1 ∧ 0 < (multat o pre x).2 := by
  induction o with
  | nil =>
    intro pre x
    have h0 : multat ([] : Overlay) pre x = fone := rfl
    rw [h0]; exact ⟨Nat.one_pos, Nat.one_pos⟩
  | cons e es ih =>
    intro pre x
    have hm' : ∀ e' ∈ es, 0 < e'.2.2.1 ∧ 0 < e'.2.2.2 :=
      fun e' he' => hm e' (List.mem_cons_of_mem _ he')
    by_cases hc : e.1 = pre ∧ e.2.1 = x
    · have h1 : multat (e :: es) pre x = e.2.2 := by
        simp only [multat, if_pos hc]
      rw [h1]; exact hm e (List.mem_cons.mpr (Or.inl rfl))
    · have h1 : multat (e :: es) pre x = multat es pre x := by
        simp only [multat, if_neg hc]
      rw [h1]; exact ih hm' pre x

/-- The round trip: an overlay applied and then its inverse
    applied returns every weight to the recorded weight, as
    fractions. This is the exactness the specification claims
    for removing an overlay — no drift, no residue. -/
theorem overlay_roundtrip {t : FTable} {o : Overlay}
    (hw : ∀ pre x, 0 < (fweight t pre x).2)
    (hm : ∀ e ∈ o, 0 < e.2.2.1 ∧ 0 < e.2.2.2)
    (pre : List Tok) (x : Tok) :
    feq (fmul (aweight t o pre x) (multat (invov o) pre x))
      (fweight t pre x) := by
  have hpos := multat_pos hm pre x
  have hinv := multat_inv o pre x
  have step1 : feq (fmul (aweight t o pre x) (multat (invov o) pre x))
      (fmul (aweight t o pre x) (finv (multat o pre x))) :=
    fmuleq (feqrefl _) hinv
  have step2 : feq (fmul (aweight t o pre x) (finv (multat o pre x)))
      (fmul (fweight t pre x)
        (fmul (multat o pre x) (finv (multat o pre x)))) :=
    fmulassoc _ _ _
  have step3 : feq (fmul (fweight t pre x)
        (fmul (multat o pre x) (finv (multat o pre x))))
      (fmul (fweight t pre x) fone) :=
    fmuleq (feqrefl _) (fmulinv _)
  have hmid1 : 0 < (fmul (aweight t o pre x)
      (finv (multat o pre x))).2 :=
    fmul_pos2 (fmul_pos2 (hw pre x) hpos.2) hpos.1
  have hmid2 : 0 < (fmul (fweight t pre x)
      (fmul (multat o pre x) (finv (multat o pre x)))).2 :=
    fmul_pos2 (hw pre x) (fmul_pos2 hpos.2 hpos.1)
  have hmid3 : 0 < (fmul (fweight t pre x) fone).2 :=
    fmul_pos2 (hw pre x) Nat.one_pos
  exact feqtrans hmid1 step1 (feqtrans hmid2 step2
    (feqtrans hmid3 step3 (fmulone _)))

/-- Pointwise fraction equal weight functions give fraction
    equal path scores. -/
theorem wscore_congr {w₁ w₂ : List Tok → Tok → Frac}
    (h : ∀ pre x, feq (w₁ pre x) (w₂ pre x)) :
    ∀ pre s, feq (wscore w₁ pre s) (wscore w₂ pre s) := by
  intro pre s
  induction s generalizing pre with
  | nil => exact feqrefl _
  | cons x xs ih => exact fmuleq (h pre x) (ih (pre ++ [x]))

/-- The empty overlay changes no score. -/
theorem overlay_empty {t : FTable} (pre : List Tok)
    (s : List Tok) :
    feq (wscore (aweight t []) pre s) (wscore (fweight t) pre s) :=
  wscore_congr (fun _ _ => fmulone _) pre s

/-- The round trip at score level: after an overlay and its
    inverse, every path scores as it scored on the recorded
    table. -/
theorem overlay_roundtrip_score {t : FTable} {o : Overlay}
    (hw : ∀ pre x, 0 < (fweight t pre x).2)
    (hm : ∀ e ∈ o, 0 < e.2.2.1 ∧ 0 < e.2.2.2)
    (pre : List Tok) (s : List Tok) :
    feq (wscore (fun p y => fmul (aweight t o p y)
      (multat (invov o) p y)) pre s) (wscore (fweight t) pre s) :=
  wscore_congr (fun p y => overlay_roundtrip hw hm p y) pre s

/-- The steps of a path: the key of each move, in order. -/
def steps (pre : List Tok) : List Tok → List (List Tok × Tok)
  | [] => []
  | x :: xs => (pre, x) :: steps (pre ++ [x]) xs

/-- Where no edit of the overlay sits at a key, the
    multiplier there is the unit. -/
theorem multat_none {o : Overlay} {pre : List Tok} {x : Tok}
    (h : ∀ e ∈ o, e.1 ≠ pre ∨ e.2.1 ≠ x) :
    multat o pre x = fone := by
  induction o with
  | nil => rfl
  | cons e es ih =>
    have hhead := h e (List.mem_cons.mpr (Or.inl rfl))
    have htail : ∀ e' ∈ es, e'.1 ≠ pre ∨ e'.2.1 ≠ x :=
      fun e' he' => h e' (List.mem_cons_of_mem _ he')
    by_cases hc : e.1 = pre ∧ e.2.1 = x
    · rcases hhead with h1 | h1
      · exact absurd hc.1 h1
      · exact absurd hc.2 h1
    · have h1 : multat (e :: es) pre x = multat es pre x := by
        simp only [multat, if_neg hc]
      rw [h1]; exact ih htail

/-- Cone invariance for the overlay route: a path whose steps
    touch no edited key scores under the overlay exactly as
    it scores on the recorded table. Derivations outside a
    rewrite's cone are not merely unchanged in outcome — their
    scores are the same fractions. -/
theorem overlay_cone {t : FTable} {o : Overlay} {pre : List Tok} :
    ∀ {s : List Tok},
    (∀ e ∈ o, ∀ st ∈ steps pre s, e.1 ≠ st.1 ∨ e.2.1 ≠ st.2) →
    feq (wscore (aweight t o) pre s) (wscore (fweight t) pre s) := by
  intro s
  induction s generalizing pre with
  | nil => intro _; exact feqrefl _
  | cons x xs ih =>
    intro h
    have hstep : ∀ e ∈ o, e.1 ≠ pre ∨ e.2.1 ≠ x :=
      fun e he => h e he (pre, x) (List.mem_cons.mpr (Or.inl rfl))
    have htail : ∀ e ∈ o, ∀ st ∈ steps (pre ++ [x]) xs,
        e.1 ≠ st.1 ∨ e.2.1 ≠ st.2 :=
      fun e he st hst => h e he st (List.mem_cons_of_mem _ hst)
    have hfac : feq (aweight t o pre x) (fweight t pre x) := by
      have hm : multat o pre x = fone := multat_none hstep
      show feq (fmul (fweight t pre x) (multat o pre x))
        (fweight t pre x)
      rw [hm]; exact fmulone _
    exact fmuleq hfac (ih htail)

/- Route one of the reweighting discipline: change what
   wins, by changing the weights on named axes. A candidate's
   axis score is the sum over its axis list of weight times
   feature; the theorems are the locality of that route. -/

/-- The axis score under a weighting: the sum over the axis
    list of weight times feature, for one candidate whose
    features are the second function. -/
def ascore (w feat : Nat → Nat) : List Nat → Nat
  | [] => 0
  | a :: as => w a * feat a + ascore w feat as

/-- Two weightings that agree on an axis list give the same
    score over it. -/
theorem ascore_agree {w₁ w₂ feat : Nat → Nat} {axes : List Nat}
    (h : ∀ a ∈ axes, w₁ a = w₂ a) :
    ascore w₁ feat axes = ascore w₂ feat axes := by
  induction axes with
  | nil => rfl
  | cons a as ih =>
    simp only [ascore]
    rw [h a (List.mem_cons.mpr (Or.inl rfl)),
      ih (fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))]

/-- Reuse equals recomputation outside the cone: a
    reweighting at one axis leaves the score over every axis
    list that excludes it exactly as a full recomputation
    computes it. The reused value is the recomputed value;
    nothing is approximated and nothing is silently stale. -/
theorem ascore_reuse {w₁ w₂ feat : Nat → Nat} {axes : List Nat}
    {a₀ : Nat} (ha0 : a₀ ∉ axes)
    (h : ∀ a, a ≠ a₀ → w₁ a = w₂ a) :
    ascore w₁ feat axes = ascore w₂ feat axes := by
  apply ascore_agree
  intro a ha
  apply h
  intro hcontra
  subst hcontra
  exact ha0 ha

/- Standing controls. Each control is a proved fact over a
   concrete table that a load bearing condition guards: if a
   future change breaks one, it has broken the condition.
   The first: greedy first step choice is not the certified
   path — the greedy engine takes the locally heaviest first
   token and lands on the lighter completion, while the
   certified decoder returns the heavier one. The second: a
   frontier bound above the best complete score blocks
   certification outright. -/

/-- The control table: two first tokens, the heavier leading
    to a light completion, the lighter to a heavy one. -/
def ctable : Table
  | [] => some [(1, 9), (2, 5)]
  | [1] => some [(3, 1)]
  | [2] => some [(4, 9)]
  | _ => none

/-- The control completeness rule. -/
def cdone : List Tok → Bool := fun s => s = [1, 3] || s = [2, 4]

/-- The greedy engine: at each step take the heaviest next
    token, never look ahead. -/
def greedy (t : Table) (done : List Tok → Bool) (pre : List Tok) :
    Nat → Option (List Tok)
  | 0 => if done pre then some pre else none
  | n + 1 => if done pre then some pre else
      match t pre with
      | none => none
      | some row => match Sel.sel (· ≤ ·) (fun e => e.2) row with
        | none => none
        | some e => greedy t done (pre ++ [e.1]) n

/-- Control: greedy is not certified. On the control table
    the greedy engine returns the completion scoring 9, the
    certified decoder returns the completion scoring 45, and
    9 is less than 45 — all three by computation. -/
theorem greedy_control :
    greedy ctable cdone [] 2 = some [1, 3] ∧
    decode ctable cdone 2 = some [2, 4] ∧
    pscore ctable [] [1, 3] < pscore ctable [] [2, 4] := by
  decide

/-- Control: an unresolved bound above the best complete
    score blocks certification. -/
theorem blocked_control : ¬ certified 5 [9] := by
  intro h
  have h9 := h 9 (List.mem_cons.mpr (Or.inl rfl))
  omega

end Prlm
