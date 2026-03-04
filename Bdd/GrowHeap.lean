/-
  GrowHeap: Extend an OBdd's heap by one dummy slot.

  This provides the "headroom" needed by HasCollectBound: for OBdd n m,
  collect has at most m elements (one per slot). Growing to OBdd n (m+1)
  adds an unreachable dummy slot, so collect still has <= m elements,
  but HasCollectBound (OBdd n (m+1)) only requires <= m. QED.
-/
import Bdd.Reduce
import Bdd.Evaluate
import Mathlib.Data.Fintype.Card

namespace GrowHeap

open Pointer

-- ============================================================================
-- Definitions
-- ============================================================================

/-- Cast a Pointer from heap size m to heap size m+1. -/
def growCastPtr : Pointer m → Pointer (m + 1)
  | .terminal b => .terminal b
  | .node j => .node j.castSucc

/-- Cast a Node from heap size m to heap size m+1. -/
def growCastNode (N : Node n m) : Node n (m + 1) :=
  ⟨N.var, growCastPtr N.low, growCastPtr N.high⟩

/-- Grow a Bdd's heap by appending one dummy slot with terminal children. -/
def growBdd (B : Bdd (n + 1) m) : Bdd (n + 1) (m + 1) :=
  ⟨(B.heap.map growCastNode).push ⟨⟨0, Nat.succ_pos n⟩, .terminal false, .terminal false⟩,
   growCastPtr B.root⟩

-- ============================================================================
-- Access lemmas
-- ============================================================================

@[simp]
theorem growCastPtr_terminal : growCastPtr (terminal b : Pointer m) = terminal b := rfl

@[simp]
theorem growCastPtr_node {j : Fin m} : growCastPtr (node j : Pointer m) = node j.castSucc := rfl

theorem growBdd_root (B : Bdd (n + 1) m) : (growBdd B).root = growCastPtr B.root := rfl

-- Fin-indexed heap access for grown BDD
theorem growBdd_heap_fin {B : Bdd (n + 1) m} {j : Fin (m + 1)} (hj : j.val < m) :
    (growBdd B).heap[j] = growCastNode (B.heap[j.val]'hj) := by
  simp only [growBdd, Fin.getElem_fin]; rw [Vector.getElem_push_lt hj]
  exact Vector.getElem_map growCastNode hj

theorem growCastNode_var (N : Node n m) : (growCastNode N).var = N.var := rfl
theorem growCastNode_low (N : Node n m) : (growCastNode N).low = growCastPtr N.low := rfl
theorem growCastNode_high (N : Node n m) : (growCastNode N).high = growCastPtr N.high := rfl

-- growCastPtr is injective
theorem growCastPtr_injective : Function.Injective (growCastPtr (m := m)) := by
  intro p q h
  cases p with
  | terminal b =>
    cases q with
    | terminal c => simp [growCastPtr] at h; exact congrArg terminal h
    | node j => simp [growCastPtr] at h
  | node j =>
    cases q with
    | terminal c => simp [growCastPtr] at h
    | node k =>
      simp [growCastPtr] at h
      exact congrArg node h

-- ============================================================================
-- SECTION 1: Reachable nodes have index < m
-- ============================================================================

-- Extract val < m from growCastPtr equation
private theorem val_lt_of_growCastPtr_eq_node {p : Pointer m} {j : Fin (m + 1)}
    (h : growCastPtr p = node j) : j.val < m := by
  cases p with
  | terminal => simp [growCastPtr] at h
  | node k => simp [growCastPtr] at h
              have := congrArg Fin.val h; simp [Fin.val_castSucc] at this; omega

-- Root node correspondence from growCastPtr equation
private theorem root_node_of_growCastPtr_eq_node {p : Pointer m} {j : Fin (m + 1)}
    (h : growCastPtr p = node j) : ∃ hj : j.val < m, p = node ⟨j.val, hj⟩ := by
  cases p with
  | terminal => simp [growCastPtr] at h
  | node k =>
    simp [growCastPtr] at h
    have hval : j.val = k.val := by
      have := congrArg Fin.val h; simp [Fin.val_castSucc] at this; omega
    exact ⟨hval ▸ k.isLt, congr_arg node (Fin.ext hval.symm)⟩

-- All reachable node indices in the grown heap have value < m.
-- (The dummy slot at index m is unreachable.)
theorem growBdd_reachable_lt {B : Bdd (n + 1) m} {j : Fin (m + 1)}
    (hr : Pointer.Reachable (growBdd B).heap (growCastPtr B.root) (node j)) :
    j.val < m := by
  suffices ∀ p, Reachable (growBdd B).heap (growCastPtr B.root) p →
      ∀ j : Fin (m + 1), p = node j → j.val < m from this _ hr j rfl
  intro p hp; induction hp with
  | refl => intro j heq; exact val_lt_of_growCastPtr_eq_node heq
  | tail _ hbc ih =>
    intro j heq; subst heq
    cases hbc with
    | low hlow =>
      next k _ =>
        simp only [growBdd_heap_fin (ih k rfl), growCastNode] at hlow
        exact val_lt_of_growCastPtr_eq_node hlow
    | high hhigh =>
      next k _ =>
        simp only [growBdd_heap_fin (ih k rfl), growCastNode] at hhigh
        exact val_lt_of_growCastPtr_eq_node hhigh

-- ============================================================================
-- SECTION 2: Ordered and toTree preservation
-- ============================================================================

-- Pointer.equiv for growCastPtr (both directions)
private theorem growCastPtr_equiv_rev (p : Pointer m) : Pointer.equiv (growCastPtr p) p := by
  constructor
  · intro b h; cases p <;> simp_all [growCastPtr]
  · intro j h; cases p with
    | terminal => simp [growCastPtr] at h
    | node k =>
      simp [growCastPtr] at h
      have hval := congrArg Fin.val h; simp [Fin.val_castSucc] at hval
      exact ⟨k, rfl, hval.symm⟩

private theorem growCastPtr_equiv (p : Pointer m) : Pointer.equiv p (growCastPtr p) := by
  constructor
  · intro b h; cases p <;> simp_all [growCastPtr]
  · intro j h; cases p with
    | terminal => simp at h
    | node k => simp at h; subst h; exact ⟨k.castSucc, rfl, Fin.val_castSucc k⟩

-- Node.equiv for growCastNode
private theorem growCastNode_equiv (N : Node n m) : Node.equiv N (growCastNode N) :=
  ⟨rfl, growCastPtr_equiv N.low, growCastPtr_equiv N.high⟩

-- Common proof: for each reachable node in the grown heap, the original node is equivalent
private theorem growBdd_node_equiv {B : Bdd (n + 1) m} {j : Fin (m + 1)}
    (hr : Reachable (growBdd B).heap (growBdd B).root (node j)) :
    ∃ hj : j.val < m, Node.equiv B.heap[j.val] (growBdd B).heap[j] := by
  have hj := growBdd_reachable_lt hr
  exact ⟨hj, by simp only [growBdd_heap_fin hj]; exact growCastNode_equiv _⟩

-- Ordered preservation via ordered_of_ordered_heap_all_reachable_eq
theorem growBdd_ordered {B : Bdd (n + 1) m} (hord : B.Ordered) : (growBdd B).Ordered :=
  Bdd.ordered_of_ordered_heap_all_reachable_eq ⟨B, hord⟩ _
    (fun _ hr => growBdd_node_equiv hr)
    (fun _ hroot => root_node_of_growCastPtr_eq_node hroot)

/-- Grow an OBdd's heap by one dummy slot. -/
def OBdd.growHeap (O : OBdd (n + 1) m) : OBdd (n + 1) (m + 1) :=
  ⟨growBdd O.1, growBdd_ordered O.2⟩

-- toTree preservation via toTree_eq_toTree_of_ordered_heap_all_reachable_eq
theorem toTree_growHeap (O : OBdd (n + 1) m) :
    OBdd.toTree (OBdd.growHeap O) = OBdd.toTree O :=
  (OBdd.toTree_eq_toTree_of_ordered_heap_all_reachable_eq O (OBdd.growHeap O)
    (fun _ hr => growBdd_node_equiv hr)
    (growCastPtr_equiv_rev O.1.root)).symm

-- evaluate preservation
open Evaluate in
theorem evaluate_growHeap (O : OBdd (n + 1) m) :
    evaluate (OBdd.growHeap O) = evaluate O := by
  simp only [evaluate_evaluate, OBdd.evaluate]
  exact congrArg _ (toTree_growHeap O)

-- ============================================================================
-- SECTION 3: HasCollectBound
-- ============================================================================

-- A nodup list of Fin (m+1) values all < m has length <= m (pigeonhole).
theorem nodup_length_le_of_forall_val_lt {l : List (Fin (m + 1))}
    (hnd : l.Nodup) (hlt : ∀ j ∈ l, j.val < m) : l.length ≤ m := by
  rcases l with _ | ⟨a, l'⟩
  · simp
  · have hm_pos : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le a.val) (hlt a (List.mem_cons_self ..))
    let g : {x : Fin (m + 1) // x ∈ (a :: l')} → Fin m :=
      fun ⟨x, hx⟩ => ⟨x.val, hlt x hx⟩
    have hg_inj : Function.Injective g := by
      intro ⟨x, hx⟩ ⟨y, hy⟩ h
      simp only [g, Fin.mk.injEq] at h
      exact Subtype.ext (Fin.ext h)
    have := (hnd.attach.map hg_inj).length_le_card
    simp [List.length_map, List.length_attach, Fintype.card_fin] at this
    exact this

-- All elements of collect on the grown heap have value < m.
theorem collect_growHeap_val_lt (O : OBdd (n + 1) m) :
    ∀ j ∈ Collect.collect (OBdd.growHeap O), j.val < m := by
  intro j hj
  rw [Collect.mem_collect_iff_reachable] at hj
  exact growBdd_reachable_lt hj

-- HasCollectBound holds for any grown OBdd.
theorem hasCollectBound_growHeap (O : OBdd (n + 1) (m + 1)) :
    Reduce.HasCollectBound (OBdd.growHeap O) := by
  simp only [Reduce.HasCollectBound]
  show (Collect.collect (OBdd.growHeap O)).length ≤ m + 1
  exact nodup_length_le_of_forall_val_lt Collect.collect_nodup (collect_growHeap_val_lt O)

-- ============================================================================
-- SECTION 4: General-purpose wrapper (handles n=0 or m=0 trivially)
-- ============================================================================

/-- Grow the heap if needed to ensure HasCollectBound. Identity when n=0 or m=0. -/
def OBdd.ensureBound (O : OBdd n m) : (m' : Nat) × OBdd n m' :=
  match n, m, O with
  | .succ _, .succ _, O => ⟨_, OBdd.growHeap O⟩
  | _, _, O => ⟨_, O⟩

theorem ensureBound_hasCollectBound : ∀ {n m} (O : OBdd n m),
    Reduce.HasCollectBound (OBdd.ensureBound O).2
  | .succ _, .succ _, O => hasCollectBound_growHeap O
  | .succ _, 0, _ => trivial
  | 0, _, _ => trivial

@[simp]
theorem ensureBound_evaluate : ∀ {n m} (O : OBdd n m),
    (OBdd.ensureBound O).2.evaluate = O.evaluate
  | .succ _, .succ _, O => by simp only [OBdd.ensureBound, OBdd.evaluate, Function.comp, toTree_growHeap]
  | .succ _, 0, _ => rfl
  | 0, _, _ => rfl

end GrowHeap
