From iris.heap_lang Require Import notation lang.


From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode.


From iris.prelude Require Import options.




Section proof.

    Context `{!heapGS Σ}.  

    
    Notation iProp := (iProp Σ).


    Lemma frame_valid (A P Q : iProp) e : 
        A ⊢ (({{{P}}} e {{{v, RET #v; Q}}}) →
        (∀ R: iProp, {{{P ∗ R}}} e {{{v, RET #v; Q ∗ R}}})).
    Proof.
        iIntros "H1 #H2".
        iIntros (R).
        iIntros (ϕ).
        iSpecialize ("H2" $! ϕ). 
        iModIntro.
        iIntros "(H1 & H3) H4".
        iSpecialize ("H2" with "H1").
        iApply "H2".
        iNext.
        iIntros (v) "H5".
        iApply "H4". 
        iSplitL "H5"; done.
    Qed.

End proof.
    
