From iris.program_logic Require Export weakestpre.

From iris.heap_lang Require Import notation lang.


From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode.


From iris.prelude Require Import options.


(* Code *)
Definition sample (y: loc) : expr := 
    let: "x" := #3 in 
         #y <- "x" + #2.


(* Spec Proof *)
Section proof.
    Context `{!heapGS Σ}.  
    Context (N : namespace).

    Notation iProp := (iProp Σ).

    Lemma sample_spec (y: loc) : 
        {{{∃ n, y ↦ #n}}} 
        sample y 
        {{{v, RET v; ⌜v = #()⌝ ∗ y ↦ #5}}}.
    Proof .
        iIntros (ϕ).  
        iIntros "H1 H2".
        unfold sample. wp_pures. 
        iDestruct "H1" as (n1) "H1".

        wp_store. iApply "H2". iSplitR.
        + iPureIntro.
          constructor.
        + iApply "H1".
    Qed.

End proof.