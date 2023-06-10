(* Generalized Stack ADT *)

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

(* Generalized Stack model *)

Fixpoint is_list_own (hd : val) (Φs : list (val → iProp)) : iProp :=
    match Φs with
    | [] => ⌜hd = NONEV⌝
    | Φ :: Φs => ∃ (ℓ:loc) x hd', ⌜hd = SOMEV #ℓ⌝ ∗ ℓ ↦ (x,hd') ∗ Φ x ∗ is_list_own hd' Φs
  end%I.

Definition is_stack_own (s : val) (Φs : list (val → iProp)): iProp :=
    (∃ (ℓ : loc) (hd : val), ⌜s = #ℓ⌝ ∗ ℓ ↦ hd ∗ is_list_own hd Φs)%I.


(* Generalized Stack specification *)
Section Stack_Spec.

    Lemma newstack_ownership_spec:
    {{{ True }}}
    new_stack #()
    {{{ s, RET s; is_stack_own s [] }}}.
    Proof.
        iIntros (ϕ) "_ HΦ".
        wp_lam.
        wp_alloc ℓ as "Hpt".
        iApply "HΦ".
        iExists ℓ, NONEV.
        iFrame; done.
    Qed.

    Lemma push_ownership_spec s Φ Φs (x : val):
    {{{ is_stack_own s Φs ∗ Φ x }}}
    push s x
    {{{ RET #(); is_stack_own s (Φ :: Φs) }}}.
    Proof.
        iIntros (Ψ) "[Hstack HΦx] HΨ".
        iDestruct "Hstack" as (ℓ hd ->) "[Hpt Hlist]".
        wp_lam; wp_let.
        wp_load.
        wp_alloc ℓ' as "Hptℓ'".
        wp_store.
        iApply "HΨ".
        iExists ℓ, (SOMEV #ℓ'); iFrame.
        iSplitR; first done.
        iExists ℓ', x, hd. by iFrame.
    Qed.

    Lemma pop_ownership_spec_nonempty s Φ Φs:
    {{{ is_stack_own s (Φ :: Φs) }}}
    pop s
    {{{x, RET (SOMEV x); Φ x ∗ is_stack_own s Φs }}}.
    Proof.
        iIntros (Ψ) "Hstack HΨ".
        iDestruct "Hstack" as (ℓ hd ->) "[Hpt Hlist]".
        iDestruct "Hlist" as (ℓ' x hd' ->) "[Hptℓ' [HΦ Hlist]]".
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
        wp_inj.
        iApply "HΨ".
        iFrame "HΦ".
        iExists ℓ, hd'; by iFrame.
    Qed.

    Lemma pop_ownership_spec_empty s:
    {{{ is_stack_own s [] }}}
    pop s
    {{{ RET NONEV; is_stack_own s [] }}}.
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
    let: "x1" := ref #1 in
    let: "x2" := ref #2 in
        push "s" "x1" ;;
        push "s" "x2" ;;
        pop "s";;
        let: "y" :=  pop "s" in
        match: "y" with
          NONE => #()
        | SOME "l" => !"l"
        end.

Definition points_to_predicate (v: val) m : iProp :=
    ∃ (l : loc),  ⌜v = #l⌝ ∗ l ↦ m.

(* Client Spec *)
Lemma client_spec :
    {{{ True }}}
    client
    {{{v, RET v; ⌜v =  #1⌝ }}}.
Proof.
    iIntros (ϕ) "_ Hϕ".
    unfold client.
    wp_bind (new_stack #()).
    iApply newstack_ownership_spec; first done.
    iNext.
    iIntros (s) "H1".
    wp_let.
    wp_alloc l1 as "H2".
    wp_let.
    wp_alloc l2 as "H3".
    wp_let.
    wp_bind (push _ _).
    Search "push_ownership_spec".
    iApply (push_ownership_spec s  with "[H1  H2]" ).
    + iSplitR "H2".
      - iAssumption. 
      - instantiate ( 1 := (fun x => points_to_predicate x #1)). 
        unfold points_to_predicate.
        iExists l1. iFrame. done.
    + iNext.
      iIntros "H1".
      wp_seq.
      wp_bind (push _ _).
      iApply (push_ownership_spec with "[H1 H3]"). 
      - iSplitL "H1"; try done.
        instantiate ( 1 := (fun x => points_to_predicate x #2)). 
        unfold points_to_predicate.
        iExists l2. iFrame. done.
      - iNext. iIntros "H1". wp_seq. wp_bind (pop _).
        Search "pop_ownership_spec_nonempty".
        iApply (pop_ownership_spec_nonempty with "H1" ).
        iNext. iIntros (x) "[H1 H2]".
        wp_seq. wp_bind (pop _). iApply (pop_ownership_spec_nonempty with "H2" ).
        iNext.
        iIntros (y) "[H2 H3]".
        wp_let.
        wp_match.
        unfold points_to_predicate.
        iDestruct "H2" as (l) "[-> H2]".
        wp_load.
        iApply "Hϕ".
        done.
Qed.
 

    