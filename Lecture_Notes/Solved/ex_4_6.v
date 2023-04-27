From iris.program_logic Require Export weakestpre.

From iris.heap_lang Require Import notation lang.


From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode.


From iris.prelude Require Import options.


(* Code *)
Definition a (l: loc) : expr :=  
         #l <- ! #l + #5.


(* Spec Proof *)
Section proof.
    Context `{!heapGS Σ}.  
    Context (N : namespace).

    Notation iProp := (iProp Σ).

    Lemma a_spec (l: loc) (n: nat) (R: iProp) : 
        {{{l ↦ #n ∗ R}}} 
        a l 
        {{{v, RET v; ⌜v = #()⌝ ∗ l ↦ #(n + 5) ∗ R}}}.
    Proof .
        iIntros (ϕ).  
        iIntros "[H1 H2] H3".
        unfold a.
        wp_load.
        wp_bind (_ + _)%E.
        wp_op.
        wp_store.
        iApply "H3".
        iFrame.
        iModIntro.
        iPureIntro.
        constructor.
    Qed.



End proof.