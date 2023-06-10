(* Sequential Counter ADT *)

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

(* Sequential Counter Specifications *)

Section Seq_Counter_Spec.

    Lemma mk_counter_spec :
    {{{ True }}}
    mk_counter #()
    {{{ l, RET #l; l ↦ #0 }}}.
    Proof.
        iIntros (ϕ).
        iIntros "_ H1".
        wp_lam.
        wp_alloc l as "H".
        iApply "H1".
        done.
    Qed.
    
    Lemma read_spec (l: loc) (m: nat):
    {{{l ↦ #m}}}
    read_counter #l
    {{{v, RET #v; ⌜v = m⌝ ∗ l ↦ #m}}}.
    Proof.
        iIntros (ϕ).
        iIntros "H1 H2".
        wp_lam.
        wp_load.
        iApply "H2".
        iFrame. done.
    Qed.

    Lemma inc_spec l (m: nat) :
    {{{ l ↦ #m}}}
    inc_counter #l
    {{{ v, RET v; ⌜v = #()⌝ ∗ l ↦ #(m + 1)}}}.
    Proof.
        iIntros (ϕ) "H1 H2".
        wp_lam.
        wp_load.
        wp_op.
        wp_store.
        iApply "H2".
        iFrame.
        done.
    Qed.

End Seq_Counter_Spec.

