From iris.program_logic Require Export weakestpre.

From iris.heap_lang Require Import notation lang.


From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode.


From iris.prelude Require Import options.




Section proof.

    Context `{!heapGS Σ}.  
    Context (N : namespace).
    
    Notation iProp := (iProp Σ).

    Definition isVal (e : expr) : Prop :=
        match e with
        | Val _ => True
        | _ => False
        end.


    Lemma fst_inference_rule (A P Q : iProp) (e : expr) (u: val) : A ⊢ (({{{P}}} e {{{v, RET v; Q}}}) →  ({{{P}}} Fst (e, u%V)  {{{v, RET v; Q}}})).
    Proof.
        iIntros "H1".
        iSimpl.
        iIntros "#H2".
        iIntros (ϕ).
        iModIntro.
        iIntros "H1 H3".
        auto.
        iSimpl.
        wp_bind ((e, u))%E.
        wp_bind (e).
        iApply ("H2" with "H1").
        iNext.
        iIntros (v) "H1".
        wp_pair.
        wp_proj.
        iApply "H3".
        done.
    Qed.
End proof.
    
