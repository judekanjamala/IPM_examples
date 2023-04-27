From iris.program_logic Require Export weakestpre.

From iris.heap_lang Require Import notation lang.
From iris.heap_lang Require Import proofmode.

From iris.proofmode Require Import proofmode.

From iris.prelude Require Import options.

Context (N : namespace).
Context `{!heapGS Σ}.  
Notation iProp := (iProp Σ).

(* Representation predicate for linked list pointed to by hd *)
Fixpoint is_list (hd: val) (zs: list val) : iProp :=
    match zs with
    | [] => ⌜hd = NONEV⌝
    | x :: xs => ∃ (l:loc) rest, ⌜hd = SOMEV #l⌝ ∗ (l ↦ (x, rest)) ∗ is_list rest xs
    end.

(* Code *)

Definition append_helper : val :=
    rec: "go" "h" "p" := 
    match: "h" with
      NONE => "p" <- (Fst (!"p"), "l2")
    | SOME "x" => "f" (Snd !"x") "x"
    end.

Definition append (go: val) : val := 
    λ: "l1" "l2",
        match: "l1" with
            NONE => "l2"
          | SOME "x" => go "l1" "x";;
                         "l1"
        end.


(* Spec Proof *)
Section proof.
    Context `{!heapGS Σ}.  
    Context (N : namespace).

    Notation iProp := (iProp Σ).



    Lemma append_spec xs ys (l l' : val) :
    {{{ is_list l xs ∗ is_list l' ys }}}
      append l l'
    {{{ v, RET v; is_list v (xs ++ ys) }}}.
    Proof.
        iIntros (ϕ).
        iIntros "[H1 H2] H3".
        iLöb as "IH" forall (l l' xs ys ϕ).
        destruct xs as [| x xs].
        + iSimplifyEq.
          wp_lam.
          wp_let. 
          wp_bind (rec: "f" "h" "p" := 
          match: "h" with
            NONE => "p" <- (Fst (!"p"), "l2")
          | SOME "x" => "f" (Snd !"x") "x"
          end).
