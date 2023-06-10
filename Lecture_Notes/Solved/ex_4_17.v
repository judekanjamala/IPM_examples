(* Swap example *)

From iris.program_logic Require Export weakestpre.

From iris.heap_lang Require Import notation lang.


From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode.


From iris.prelude Require Import options.


(* Code *)
Definition swap : val :=  
        λ: "x" "y",
            let: "z" := !"x" in
            "x" <- !"y";;
            "y" <- "z".



(* Spec Proof *)
Section proof.
    Context `{!heapGS Σ}.  
    Context (N : namespace).

    Notation iProp := (iProp Σ).

    Lemma swap_spec (x y: loc) (n1 n2: nat) : 
        {{{x ↦ #n1 ∗ y ↦ #n2}}} 
        swap #x #y 
        {{{v, RET v; ⌜v = #()⌝ ∗ x ↦ #n2 ∗ y ↦ #n1}}}.
    Proof .
        iIntros (ϕ).  
        iIntros "[H1 H2] H3".
        unfold swap.
        wp_lam.
        wp_let.
        wp_load.
        wp_let.
        wp_load.
        wp_store.
        wp_store.
        iApply "H3".
        iFrame.
        iModIntro.
        iPureIntro.
        constructor.
    Qed.



End proof.