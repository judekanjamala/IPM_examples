(* Increment List *)

From iris.program_logic Require Export weakestpre.

From iris.heap_lang Require Import notation lang.
From iris.heap_lang Require Import proofmode.

From iris.proofmode Require Import proofmode.

From iris.prelude Require Import options.

Context (N : namespace).
Context `{!heapGS Σ}.  
Notation iProp := (iProp Σ).

(* Code *)
Definition inc_list : val :=  
        rec: "inc" "hd" := 
            match: "hd" with
              NONE => #()
            | SOME "l" => 
                let: "x" := Fst !"l" in
                let: "rest" := Snd !"l" in
                    "l" <- ("x" + #1, "rest");;
                    "inc" "rest"
            end.

Fixpoint isList (hd: val) (zs: list val) : iProp :=
    match zs with
    | [] => ⌜hd = NONEV⌝
    | x :: xs => ∃ (l:loc) rest, ⌜hd = SOMEV #l⌝ ∗ (l ↦ (x, rest)) ∗ isList rest xs
    end.


Fixpoint isListNat (hd: val) (zs: list Z) : iProp :=
    match zs with
    | [] => ⌜hd = NONEV⌝
    | x :: xs => ∃ (l:loc) rest, ⌜hd = SOMEV #l⌝ ∗ (l ↦ (#x, rest)) ∗ isListNat rest xs
    end.
    

(*Spec Proof*)

Section proof.
    
    Lemma inc_list_spec (hd: val) (zs: list Z) :
        {{{isListNat hd zs}}}
        inc_list hd 
        {{{v, RET v; ⌜v = #()⌝ ∗ isListNat hd (List.map Z.succ zs)}}}.
    Proof.
        iIntros (ϕ).
        iIntros "H1 H2".
        iLöb as "IH" forall (hd zs ϕ).
        wp_rec.
        destruct zs as [| y ys]. 
        + iSimplifyEq.
          wp_match.
          iApply "H2".
          done.
        + iSimplifyEq. 
          iDestruct "H1" as (l rest Heq) "[H1 H3]".
          rewrite Heq.
          wp_match. 
          wp_load. 
          wp_proj.
          wp_let.
           wp_bind (Snd ! #l).
           wp_load.
           wp_pure.
           wp_let.
           wp_store.
           iApply ("IH" with "H3").
           iNext.
           iIntros (v) "[H3 H4]".
           iApply "H2".
           iFrame.
           iExists l. iExists rest. iFrame. done.
    Qed.

End proof.

