/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Automata.MPDA.Holes
public import CslibFrontier.Foundations.Data.List.Extract

/-! # Context-, round- and scope-bounded sequences of multistack pushdown automata

Reachability for multistack pushdown automata is undecidable, so verification focuses on
restricted classes of runs. Section 2 of [AkshayGastinKrishnaRoychowdhury2020] recalls the
classes that hole-bounded sequences generalize:

- `MPDA.ContextBounded`: at most `K` contexts, where a context uses at most one stack.
- `MPDA.RoundBounded`: at most `K` rounds, where a round is one possibly empty context for each
  stack `0, …, n - 1`, in this order.
- `MPDA.ScopeBounded`: at most `K` context switches between a push and its matching pop.

## Main definitions

- `MPDA.Splits`: a sequence is the concatenation of at most `K` factors with a given property.
- `MPDA.IsContext`, `MPDA.IsRound`: contexts and rounds.
- `MPDA.ContextBounded`, `MPDA.RoundBounded`, `MPDA.ScopeBounded`.

## Main results

- `MPDA.Splits.card_le`: a set of positions no two of which lie in a common factor has at most as
  many elements as there are factors.
- `MPDA.RoundBounded.contextBounded`: `K` rounds give at most `K * n` contexts.
- `MPDA.ContextBounded.scopeBounded`: a sequence with at most `K` contexts is `K`-scope-bounded.

## Implementation notes

Positions are `0`-indexed. The scope of a matched push and pop is measured by the number of
contexts of the factor from the push to the pop: `K` context switches means `K + 1` contexts.

## References

* [S. Akshay, P. Gastin, S. Krishna, S. Roychowdhury,
  *Revisiting Underapproximate Reachability for Multipushdown Systems*]
  [AkshayGastinKrishnaRoychowdhury2020]
-/

public section

namespace Cslib.Automata.MPDA

variable {n : ℕ} {Γ α β : Type*}

/-! ## Bounded splittings -/

/-- `Splits P K w` holds when `w` is the concatenation of at most `K` factors satisfying `P`. -/
@[expose] def Splits (P : List β → Prop) (K : ℕ) (w : List β) : Prop :=
  ∃ ws : List (List β), ws.length ≤ K ∧ ws.flatten = w ∧ ∀ v ∈ ws, P v

namespace Splits

variable {P Q : List β → Prop} {K K' : ℕ} {w : List β}

private theorem mono_bound (h : Splits P K w) (hK : K ≤ K') : Splits P K' w :=
  let ⟨ws, hlen, hw, hP⟩ := h
  ⟨ws, hlen.trans hK, hw, hP⟩

private theorem mono (h : Splits P K w) (hPQ : ∀ v, P v → Q v) : Splits Q K w :=
  let ⟨ws, hlen, hw, hP⟩ := h
  ⟨ws, hlen, hw, fun v hv => hPQ v (hP v hv)⟩

private theorem flatten_of_forall {m : ℕ} :
    ∀ ws : List (List β), (∀ v ∈ ws, Splits P m v) → Splits P (ws.length * m) ws.flatten
  | [], _ => ⟨[], Nat.zero_le _, rfl, by simp⟩
  | v :: ws, h => by
    obtain ⟨us, hlen, rfl, hP⟩ := h v List.mem_cons_self
    obtain ⟨us', hlen', hw', hP'⟩ :=
      flatten_of_forall ws fun v hv => h v (List.mem_cons_of_mem _ hv)
    refine ⟨us ++ us', ?_, ?_, ?_⟩
    · rw [List.length_append, List.length_cons, Nat.succ_mul]
      omega
    · rw [List.flatten_append, hw', List.flatten_cons]
    · intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact hP u hu
      · exact hP' u hu

/-- A splitting into factors that themselves split boundedly gives a bounded splitting. -/
private theorem trans {m : ℕ} (h : Splits (Splits P m) K w) : Splits P (K * m) w := by
  obtain ⟨ws, hlen, rfl, hP⟩ := h
  exact (flatten_of_forall ws hP).mono_bound (Nat.mul_le_mul_right m hlen)

private theorem prefix_aux (hP : ∀ u v, u <+: v → P v → P u) :
    ∀ (ws : List (List β)) (u : List β), (∀ v ∈ ws, P v) → u <+: ws.flatten →
      ∃ us : List (List β), us.length ≤ ws.length ∧ us.flatten = u ∧ ∀ v ∈ us, P v
  | [], u, _, hu => ⟨[], le_rfl, (List.prefix_nil.mp hu).symm, by simp⟩
  | v :: ws, u, hws, ⟨t, ht⟩ => by
    rw [List.flatten_cons] at ht
    rcases List.append_eq_append_iff.mp ht with ⟨a, rfl, -⟩ | ⟨c, rfl, hc⟩
    · exact ⟨[u], by simp, by simp,
        by simpa using hP u (u ++ a) (List.prefix_append u a) (hws _ List.mem_cons_self)⟩
    · obtain ⟨us, hlen, rfl, hus⟩ := prefix_aux hP ws c
        (fun v hv => hws v (List.mem_cons_of_mem _ hv)) ⟨t, hc.symm⟩
      refine ⟨v :: us, by simpa using hlen, by simp, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hws _ List.mem_cons_self
      · exact hus x hx

private theorem suffix_aux (hP : ∀ u v, u <:+ v → P v → P u) :
    ∀ (ws : List (List β)) (u : List β), (∀ v ∈ ws, P v) → u <:+ ws.flatten →
      ∃ us : List (List β), us.length ≤ ws.length ∧ us.flatten = u ∧ ∀ v ∈ us, P v
  | [], u, _, hu => ⟨[], le_rfl, (List.suffix_nil.mp hu).symm, by simp⟩
  | v :: ws, u, hws, ⟨t, ht⟩ => by
    rw [List.flatten_cons] at ht
    rcases List.append_eq_append_iff.mp ht with ⟨a, rfl, rfl⟩ | ⟨c, rfl, hc⟩
    · refine ⟨a :: ws, by simp, by simp, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hP x (t ++ x) (List.suffix_append t x) (hws _ List.mem_cons_self)
      · exact hws x (List.mem_cons_of_mem _ hx)
    · obtain ⟨us, hlen, rfl, hus⟩ := suffix_aux hP ws u
        (fun v hv => hws v (List.mem_cons_of_mem _ hv)) ⟨c, hc.symm⟩
      exact ⟨us, by simp only [List.length_cons]; omega, rfl, hus⟩

/-- If `P` is closed under taking infixes, so is having a splitting into at most `K` factors
satisfying `P`. -/
private theorem of_isInfix (hP : ∀ u v, u <:+: v → P v → P u) (h : Splits P K w) {u : List β}
    (hu : u <:+: w) : Splits P K u := by
  obtain ⟨ws, hlen, rfl, hws⟩ := h
  obtain ⟨t, ht, hts⟩ := List.infix_iff_prefix_suffix.mp hu
  obtain ⟨vs, hvlen, rfl, hvs⟩ :=
    suffix_aux (fun u v h => hP u v h.isInfix) ws t hws hts
  obtain ⟨us, hulen, rfl, hus⟩ :=
    prefix_aux (fun u v h => hP u v h.isInfix) vs _ hvs ht
  exact ⟨us, (hulen.trans hvlen).trans hlen, rfl, hus⟩

private theorem card_le_aux (hP : ∀ u v, u <:+: v → P v → P u) :
    ∀ ws : List (List β), (∀ v ∈ ws, P v) → ∀ T : Finset ℕ,
      (∀ t ∈ T, t < ws.flatten.length) →
      (∀ t ∈ T, ∀ t' ∈ T, t < t' → ¬P (ws.flatten.extract t (t' + 1))) → T.card ≤ ws.length
  | [], _, T, hT, _ => by
    rw [Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem fun t ht => by
      simpa using hT t ht)]
    simp
  | v :: ws, hws, T, hT, hTP => by
    rw [List.flatten_cons] at hT hTP
    rw [← Finset.card_filter_add_card_filter_not (p := fun t => t < v.length), List.length_cons]
    suffices h : (T.filter fun t => t < v.length).card ≤ 1 ∧
        (T.filter fun t => ¬t < v.length).card ≤ ws.length by omega
    refine ⟨?_, ?_⟩
    · rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter] at ha hb
      by_contra hab
      wlog hlt : a < b generalizing a b
      · exact this b a hb ha (Ne.symm hab) (by omega)
      apply hTP a ha.1 b hb.1 hlt
      rw [extract_append_right _ _ (by omega)]
      exact hP _ _ (List.extract_isInfix v _ _) (hws v List.mem_cons_self)
    · have hinj : Set.InjOn (fun t => t - v.length)
          (T.filter fun t => ¬t < v.length : Finset ℕ) := by
        intro a ha b hb hab
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha hb
        simp only at hab
        omega
      rw [← Finset.card_image_of_injOn hinj]
      refine card_le_aux hP ws (fun u hu => hws u (List.mem_cons_of_mem _ hu)) _ ?_ ?_
      · intro t ht
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
        simp only [Finset.mem_filter] at hs
        have := hT s hs.1
        simp only [List.length_append] at this
        omega
      · intro t ht t' ht' hlt
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
        obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp ht'
        simp only [Finset.mem_filter] at hs hs'
        have := hTP s hs.1 s' hs'.1 (by omega)
        rwa [show s = v.length + (s - v.length) by omega,
          show s' + 1 = v.length + (s' - v.length + 1) by omega,
          extract_append_left] at this

/-- If `w` splits into at most `K` factors satisfying an infix-closed `P`, then every set `T` of
positions of `w` such that no two of them lie in a common factor satisfying `P` has at most `K`
elements. -/
theorem card_le (hP : ∀ u v, u <:+: v → P v → P u) (h : Splits P K w) (T : Finset ℕ)
    (hT : ∀ t ∈ T, t < w.length)
    (hTP : ∀ t ∈ T, ∀ t' ∈ T, t < t' → ¬P (w.extract t (t' + 1))) : T.card ≤ K := by
  obtain ⟨ws, hlen, rfl, hws⟩ := h
  exact (card_le_aux hP ws hws T hT hTP).trans hlen

end Splits

/-! ## Contexts and rounds -/

/-- The stack touched by an operation, if any. -/
@[expose] def Op.stack : Op n Γ → Option (Fin n)
  | .nop => none
  | .push i _ => some i
  | .pop i _ => some i

/-- Every operation of `w` touches stack `i` or no stack. -/
@[expose] def IsContextOf (i : Fin n) (w : List (α × Op n Γ)) : Prop :=
  ∀ μ ∈ w, μ.2.stack = none ∨ μ.2.stack = some i

/-- A context is a sequence of transitions that uses at most one stack. -/
@[expose] def IsContext (w : List (α × Op n Γ)) : Prop :=
  ∃ o : Option (Fin n), ∀ μ ∈ w, μ.2.stack = none ∨ μ.2.stack = o

/-- A round is a sequence of contexts for stacks `0, …, n - 1`, in this order. Each context may be
empty. -/
@[expose] def IsRound (w : List (α × Op n Γ)) : Prop :=
  ∃ vs : Fin n → List (α × Op n Γ), (List.ofFn vs).flatten = w ∧ ∀ i, IsContextOf i (vs i)

/-- At most `K` contexts. -/
@[expose] def ContextBounded (K : ℕ) (w : List (α × Op n Γ)) : Prop := Splits IsContext K w

/-- At most `K` rounds. -/
@[expose] def RoundBounded (K : ℕ) (w : List (α × Op n Γ)) : Prop := Splits IsRound K w

theorem IsContext.of_isInfix {u w : List (α × Op n Γ)} (hu : u <:+: w) (h : IsContext w) :
    IsContext u :=
  let ⟨o, ho⟩ := h
  ⟨o, fun μ hμ => ho μ (hu.subset hμ)⟩

private theorem IsRound.contextBounded {w : List (α × Op n Γ)} (h : IsRound w) :
    ContextBounded n w := by
  obtain ⟨vs, rfl, hvs⟩ := h
  refine ⟨List.ofFn vs, by simp, rfl, ?_⟩
  intro v hv
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
  exact ⟨some i, hvs i⟩

/-- `K` rounds give at most `K * n` contexts. -/
theorem RoundBounded.contextBounded {K : ℕ} {w : List (α × Op n Γ)} (h : RoundBounded K w) :
    ContextBounded (K * n) w :=
  (h.mono fun _ hv => hv.contextBounded).trans

private theorem ContextBounded.of_isInfix {K : ℕ} {u w : List (α × Op n Γ)}
    (h : ContextBounded K w) (hu : u <:+: w) : ContextBounded K u :=
  Splits.of_isInfix (fun _ _ huv hv => hv.of_isInfix huv) h hu

/-! ## Scope-bounded sequences -/

/-- A sequence is `K`-scope-bounded if every push and its matching pop are separated by at most `K`
context switches, that is, the factor from the push to the pop splits into at most `K + 1`
contexts. -/
@[expose] def ScopeBounded (K : ℕ) (w : List (α × Op n Γ)) : Prop :=
  ∀ p m, Matches w p m → ContextBounded (K + 1) (w.extract p (m + 1))

/-- A sequence with at most `K` contexts is `K`-scope-bounded. -/
theorem ContextBounded.scopeBounded {K : ℕ} {w : List (α × Op n Γ)} (h : ContextBounded K w) :
    ScopeBounded K w :=
  fun p m _ => (h.of_isInfix (w.extract_isInfix p (m + 1))).mono_bound (Nat.le_succ K)

end Cslib.Automata.MPDA
