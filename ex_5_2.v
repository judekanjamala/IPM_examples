From iris.program_logic Require Export weakestpre.

From iris.heap_lang Require Import notation lang.
From iris.heap_lang Require Import proofmode.

From iris.proofmode Require Import proofmode.

From iris.prelude Require Import options.

Context (N : namespace).
Context `{!heapGS Σ}.  
Notation iProp := (iProp Σ).



(* List Model *)

Fixpoint is_list (hd : val) (xs : list val) : iProp :=
  match xs with
  | [] => ⌜hd = NONEV⌝
  | x :: xs => ∃ (l:loc) hd', ⌜hd = SOMEV #l⌝ ∗ l ↦ (x,hd') ∗ is_list hd' xs
end%I.

Fixpoint is_list_nat (hd : val) (xs : list Z) : iProp :=
    match xs with
    | [] => ⌜hd = NONEV⌝
    | x :: xs => ∃ (l:loc) hd', ⌜hd = SOMEV #l⌝ ∗ l ↦ (#x,hd') ∗ is_list_nat hd' xs
    end%I.
    
(* Sample Definition *)

Fixpoint sum_list (l: list nat) : nat :=
    match l with
    | [] => 0
    | x :: xs => x + (sum_list xs) 
    end.

Definition foldr : val :=
    rec: "foldr" "f" "a" "l" :=
      match: "l" with
        NONE => "a"
      | SOME "p" =>
        let: "hd" := Fst !"p" in
        let: "t" := Snd !"p" in
        "f" ("hd", ("foldr" "f" "a" "t"))
      end.

Definition sample: val :=
    λ: "p",  
        let: "x" := Fst "p" in
        let: "y" := Snd "p" in
          ▷    "x" + "y".

Section sample_spec_proof.
    
    Lemma sample_spec (a x: nat) (ys: list nat):
        {{{ ⌜a = sum_list ys⌝ }}}
        sample (#x, #a)
        {{{v, RET v; ⌜v = #(sum_list (x :: ys)%Z)⌝}}}.
    Proof.
        iIntros (ϕ) "H1 H2".
        wp_bind ((_, _)%E).
        wp_pair.
        wp_lam.
        wp_bind (Fst _).
        wp_proj.
        wp_let.
        wp_bind (Snd _).
        wp_proj.
        wp_let.
        wp_op.
        simpl.
        iDestruct "H1" as "<-".
        iApply "H2".
        iModIntro.
        iPureIntro.
        apply f_equal.
        auto.
        
        congruence.
        rewrite -> (N2Z.inj (x + a) (x + a)).
        remember (x + a) as y.

        constructor.
        injection.
        rewrite <- Heqy.
        done.
        trivial.
        constructor. 

        iSpecialize ("H2" ) as #.
        iApply ("H2" (x + a) ).
        constructor.
        done.

        unfold sample.
        wp_lam.

    Qed.


End sample_spec_proof.
