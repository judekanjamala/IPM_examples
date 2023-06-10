(* Modular Sequential Counter ADT *)

From iris.program_logic Require Export weakestpre.

From iris.heap_lang Require Import notation lang.
From iris.heap_lang Require Import proofmode.

From iris.proofmode Require Import proofmode.

From iris.prelude Require Import options.

Context (N : namespace).
Context `{!heapGS Σ}.  
Notation iProp := (iProp Σ).

(* Sequential Counter*)

Definition mk_counter : val :=
    λ: <> , ref #0.

Definition read_counter : val :=
    λ: "l", !"l".

Definition inc_counter : val :=
    λ: "l", "l" <- !"l" + #1.

(* Counter Model *)
Definition is_counter (c: val) (n: Z) :iProp := ∃ (l: loc), ⌜c = #l⌝ ∗ l ↦ #n.


(* Sequential Counter Specifications using predicate *)

Section Seq_Modular_Counter_Spec.

    Lemma Counter_Module_Spec :
    {{{ True }}}
    mk_counter #()
    {{{v, RET v; is_counter v 0 }}}.
    Proof. 
        iIntros (ϕ) "H1 H2".
        wp_lam.
        wp_alloc l as "H3".
        iApply "H2".
        iExists l.
        iFrame.
        done.
    Qed.

    Lemma read_spec (l: loc) (m: nat):
    {{{ is_counter #l m}}}
    read_counter #l
    {{{v, RET #v; ⌜v = m⌝ ∗ is_counter #l m}}}.
    Proof.
        iIntros (ϕ).
        iIntros "H1 H2".
        wp_lam.
        iDestruct "H1" as (l' ->) "H1".
        wp_load.
        iApply "H2".
        iSplitR.
        + done.
        + iExists l'. iFrame. done.
    Qed.

    Lemma inc_spec l (m: nat) :
    {{{ is_counter #l m }}}
    inc_counter #l
    {{{ v, RET v; ⌜v = #()⌝ ∗ is_counter #l (m + 1)}}}.
    Proof.
        iIntros (ϕ) "H1 H2".
        iDestruct "H1" as (l' ->) "H1".
        wp_lam.
        wp_load.
        wp_op.
        wp_store.
        iApply "H2".
        iFrame.
        iSplitR.
        + done.
        + iExists l'. iFrame. done.
    Qed.

End Seq_Modular_Counter_Spec.
