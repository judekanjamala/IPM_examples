From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export notation lang.
From iris.proofmode Require Export proofmode.
From iris.heap_lang Require Import proofmode.
From iris.prelude Require Import options.

Context (N : namespace).
Context `{!heapGS Σ}.  
Notation iProp := (iProp Σ).


(* Stack methods definitions *)

Definition new_stack : val := λ: <>, ref NONEV.

Definition push : val := λ: "s", λ: "x",
                        let: "hd" := !"s" in
                        let: "p" := ("x", "hd") in
                        "s" <- SOME (ref "p").

Definition pop : val := (λ: "s",
                        let: "hd" := !"s" in
                        match: "hd" with
                            NONE => NONE
                        | SOME "l" =>
                            let: "p" := !"l" in
                            let: "x" := Fst "p" in
                            "s" <- Snd "p" ;; SOME "x"
                        end).

(* Stack model *)

Fixpoint is_list (hd : val) (xs : list val) : iProp :=
    match xs with
    | [] => ⌜hd = NONEV⌝
    | x :: xs => ∃ (ℓ: loc) hd', ⌜hd = SOMEV #ℓ⌝ ∗ ℓ ↦ (x,hd') ∗ is_list hd' xs
    end%I.


Definition is_stack (s : val) (xs : list val): iProp :=
    (∃ (ℓ : loc) (hd : val), ⌜s = #ℓ⌝ ∗ ℓ ↦ hd ∗ is_list hd xs)%I.


(* Sequential Stack specification *)
Section Stack_Spec.

    Lemma new_stack_spec:
    {{{ True }}}
        new_stack #()
        {{{ s, RET s; is_stack s [] }}}.
    Proof.
    iIntros (ϕ) "_ HΦ".
    wp_lam.
    wp_alloc ℓ as "Hpt".
    iApply "HΦ".
    iExists ℓ, NONEV.
    iFrame; done.
    Qed.

    Lemma push_spec s xs (x : val):
    {{{ is_stack s xs }}}
        push s x
        {{{ RET #(); is_stack s (x :: xs) }}}.
    Proof.
    iIntros (ϕ) "Hstack HΦ".
    iDestruct "Hstack" as (ℓ hd ->) "[Hpt Hlist]".
    wp_lam. wp_let.
    wp_load.
    wp_let.
    wp_pair.
    wp_let.
    wp_alloc ℓ' as "Hptℓ'".
    wp_store.
    iApply "HΦ".
    iExists ℓ, (SOMEV #ℓ'); iFrame.
    iSplitR; first done.
    iExists ℓ', hd; by iFrame.
    Qed.

    Lemma pop_spec_nonempty s (x : val) xs:
    {{{ is_stack s (x :: xs) }}}
        pop s
        {{{ RET (SOMEV x); is_stack s xs }}}.
    Proof.
    iIntros (ϕ) "Hstack HΦ".
    iDestruct "Hstack" as (ℓ hd ->) "[Hpt Hlist]".
    iDestruct "Hlist" as (ℓ' hd' ->) "[Hptℓ' Hlist]".
    wp_lam.
    wp_load.
    wp_let.
    wp_match.
    wp_load.
    wp_let.
    wp_proj.
    wp_let.
    wp_proj.
    wp_store.
    wp_pures.
    iApply "HΦ".
    iExists ℓ, hd'; by iFrame.
    Qed.


Lemma pop_spec_empty s:
  {{{ is_stack s [] }}}
    pop s
    {{{ RET NONEV; is_stack s [] }}}.
Proof.
  iIntros (ϕ) "Hstack HΦ".
  iDestruct "Hstack" as (ℓ hd ->) "[Hpt %]"; subst.
  wp_lam.
  wp_load.
  wp_pures.
  iApply "HΦ".
  iExists ℓ, NONEV; by iFrame.
Qed.

End Stack_Spec.

(* Client Code *)

Definition client : expr :=
    let: "s" := new_stack #() in
    push "s" #1 ;;
    push "s" #2 ;;
    pop "s";;
    pop "s".

(* Client Spec *)

Lemma client_spec :
    {{{ True }}}
    client
    {{{v, RET v; ⌜v = (SOMEV #1)%V⌝ }}}.
    Proof.
    iIntros (ϕ) "_ Hϕ".
    unfold client.
    wp_bind (new_stack #()).
    iApply new_stack_spec; first done.
    iNext.
    iIntros (s) "H1".
    wp_let.
    do 2 (
    wp_bind (push _ _);
    iApply (push_spec with "H1" );
    iNext;
    iIntros "H1";
    wp_seq).
    do 2 (
    wp_bind (pop _);
    iApply (pop_spec_nonempty with "H1");
    iNext;
    iIntros "H1";
    try wp_seq).
    
    iApply "Hϕ".
    done.
Qed.

    