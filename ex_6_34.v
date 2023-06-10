(*  "parallel increment" for 3 threads. *)

 From iris.algebra Require Import frac.
 From iris.proofmode Require Import proofmode.
 From iris.base_logic.lib Require Export invariants.
 From iris.program_logic Require Export weakestpre.
 From iris.heap_lang Require Import proofmode.
 From iris.heap_lang Require Import notation lang.
 From iris.heap_lang.lib Require Import par.
 From iris.prelude Require Import options.
 
 
 (* SF RA definition is taken from lecture_notes.sfra.v. *)
 
 From iris.algebra Require Import frac.
 
 Section RADefinitions.
 
 Inductive SF :=
     | S (* The starting state *)
     | F (* The final state *)
     | B. (* The invalid element "bottom" *)
 
 Canonical Structure SFRAC := leibnizO SF.
 
 
 Global Instance SFRAop : Op SF :=
   λ x y, match x, y with
            | F, F => F
            | _, _ => B end.
 
 Global Instance SFRAValid : Valid SF :=
   λ x, match x with
        | S | F => True
        | _ => False end.
 
 Global Instance SFRACore : PCore SF :=
   λ _, None.
 
 (* Produce cameras from the RA *)
 Definition SFRA_mixin : RAMixin SF.
 Proof.
     split; try apply _; try done.
     (* The operation is associative. *)
     - unfold op, SFRAop. intros [] [] []; reflexivity.
     (* The operation is commutative. *)
     - unfold op, SFRAop. intros [] []; reflexivity.
     - (* Validity axiom: validity is down-closed with respect to the 
          extension order. *)
       intros [] []; intros H; try (inversion H); auto.
 Qed.
 
 Canonical Structure SFRA := discreteR SF SFRA_mixin.
 
 Global Instance SFRA_cmra_discrete : CmraDiscrete SFRA.
 Proof. apply discrete_cmra_discrete. Qed.
 
 Global Instance SFRA_S_exclusive : Exclusive S.
 Proof. intros x. done. Qed.
 
 (* States the duplicability of F. Alternatively can use "replace". NOTE: Usually
    would make F a core element of the resource algebra, which would make it
    persistent and thereby duplicable *)
 Lemma SFRA_FF: F = F ⋅ F.
 Proof.
   done.
 Qed.
 
 Lemma SFRA_update : (S : SF) ~~> F.
 Proof.
   apply cmra_update_exclusive.
   done.
   (* *** Manual proof *** *)
   (* unfold "~~>". *)
   (* intros n mx. *)
   (* destruct mx as [x |]. *)
   (* - destruct x; contradiction. *)
   (* - done. *)
 Qed.
 
 Class SFG Σ := SF_G :> inG Σ (SFRA).
 Class FracG Σ := Frac_G :> inG Σ (fracR).
 
 End RADefinitions.
 
 
 (* This section defines some basic lemmas that 
    make using the resource algebras more practical. *)
 Section RALemmas.
   Context (N : namespace).
   Context `{!SFG Σ}.
   Context `{!FracG Σ}.
 
 Lemma own_frac_valid γ (x : Qp): own γ x ⊢ ⌜(x ≤ 1)%Qp⌝.
 Proof.
   rewrite own_valid.
   iIntros "!%".
   apply frac_valid.
 Qed.
 
 Lemma own_SFRA_FF (γ: gname): own γ F ⊣⊢ own γ F ∗ own γ F.
 Proof.
   apply (own_op _ F F).
   (* Alternative proof using lemmas from above *)
   (* rewrite -own_op. *)
   (* rewrite -SFRA_FF. *)
   (* reflexivity. *)
 Qed.
 
 (* This lemma states the incompatibility of S and F *)
 Lemma own_SF_false (γ: gname): own γ S ∗ own γ F ⊢ False.
 Proof.
   rewrite -own_op.
   rewrite own_valid.
   iIntros (Contra).
   contradiction.
 Qed.
 
 End RALemmas.
 
 
 (* Definition of the program *)
 Definition incr (ℓ : loc) : expr := #ℓ <- !#ℓ + #1.
 

 (* Proof adapted from the case for 2 threads from parallel_inc.v *)
 Section proof.
   Context `{!heapGS Σ}.
   Context `{!spawnG Σ}.
   Notation iProp := (iProp Σ).
   Context (N : namespace).
   (* We have to add the resource algebra classes to the context *)
   Context `{!SFG Σ}.
   Context `{!FracG Σ}.
 
(* Ghost State Construction

  To get a specification which precisely reflects the possible outcomes of the
  parallel increment, we use ghost state in an invariant to represent the possible
  states during an execution. The ghost state consists of two parts from two
  different resource algebras which we use in parallel:
  - A transition system (resource algebra SF) with the tokens S and F, where S can be
    updated to F, F is duplicable, and everything else except F⋅F is incompatible
  - Three 1/3 fractions, which can be combined into 1

  The transition system is used to keep track of whether we are in the starting state
  (S), which cannot exist at the end of execution, or one of the three final states
  (F), which are possible at the end of execution. However, to be able to state that
  the location will be incremented by exactly 1 or 2 or 3 after execution of the
  program, we also have to keep track of how many times the value has been logically
  incremented. To this end, we use three 1/3 fractions, which, owned by the threads,
  initially represent the ability to increment, and when given to the invariant, they
  represent the number of contributions of "+1" to the value at location ℓ.
*)

(* 
  The invariant consists of 4 disjuncts:
  - the starting state, where ℓ points to n, represented by the ownership of the S
    token
  - the first final state, where ℓ points to n+1, represented by the ownership of
    an F token and a 1/3 token, which stands for one contribution of 1 to the value
    at ℓ
  - the second final state, where ℓ points to n+2, represented by the ownership of
    an F token and two 1/3 tokens, that is, a 2/3 token, which stands for two
    contributions of 1 to the value at ℓ.
  - the third final state, where ℓ points to n+2, represented by the ownership of
    an F token and three 1/3 tokens, that is, a 1 token, which stands for three
    contributions of 1 to the value at ℓ.
*)
 
 Definition incr_inv (ℓ : loc) (γ1 γ2 : gname) (n : Z) : iProp :=
     ℓ ↦ #n ∗ own γ1 S
   ∨ ℓ ↦ #(n+1) ∗ own γ1 F ∗ own γ2 (1/3)%Qp
   ∨ ℓ ↦ #(n+2) ∗ own γ1 F ∗ own γ2 (2/3)%Qp
   ∨ ℓ ↦ #(n+3) ∗ own γ1 F ∗ own γ2 1%Qp.
 

 (* Overview of the proof

    The proof starts with allocating ghost state: S from the SF resource algebra, and
    1 from the fractional resource algebra. We are then able to allocate the
    invariant in the first state, using the fact that ℓ points to n at the beginning
    and that we own the S token. From this point on, we can proceed separately in
    each thread. Here we will make use of the three 1/3 fractions we own, passing one
    to each thread. This means that each thread has the possibility to contribute +1
    to the value stored at location ℓ. As both threads are the same, we can extract a
    specification for the code of a single thread and then use it to prove our actual
    specification. As the location ℓ to be modified is governed by an invariant, it
    can be used by both threads simultaneously without having to think of
    interleavings in the proof. This nicely demonstrates the modularity of the logic,
    allowing us to verify parallel components separately.

    Each thread is then verified by receiving the invariant and a 1/3 token as
    resources. To read the current value from the location and to write the updated
    value back, we need to open the invariant. As the invariant can only be opened
    for an atomic step, it has to be opened and closed twice, once for reading and
    once for writing. Each time, we have to consider all possible states the
    invariant can be in and then have to show that one of the cases holds when
    closing it. Depending on where we are in the program (reading the value or
    storing the updated value) only some of the cases will be possible. The
    impossible cases will be ruled out using the definition of the resource algebras,
    namely by obtaining invalid elements, resulting in a precondition being False.
 *)
 
 Lemma div_2_3  : ((1 / 3 + 1 / 3 = 2 / 3)%Qp)%I.
 Proof.
   Admitted.

 (* Proving a spec for the threads *)
 Lemma incr_spec (ℓ : loc) (n : Z) (γ1 γ2 : gname):
   {{{ inv N (incr_inv ℓ γ1 γ2 n) ∗ own γ2 (1 / 3)%Qp }}}
     incr ℓ
   {{{ v, RET #v; own γ1 F }}}.
 Proof.
   iIntros (Φ) "[#Inv Own1/3] Post".
   unfold incr.
   (* To prove that the increment results in an F token, we have to prove two
      triples, one for reading the value currently stored at ℓ, and then one for
      storing the incremented value. To prove each triple, we have to open the
      invariant to get access to ℓ, and then close it again after the one atomic
      step. *)
   wp_bind (!#ℓ)%E.
   (* In the first triple, we find out the value stored in l. It can be n or n + 1 or
      n + 2. The disjunct n + 3 will be ruled out by token 1/3 in our possession
      since it will exceed 1. This information we want to use as an assumption in the
      second triple. Thus we use wp_wand to update the current postcondition
      accordingly. However, we will not consume this resource, so we restate the
      ownership in the postcondition. *)
   iApply ((wp_wand _ _ _ (fun v => (⌜v = #n⌝ ∨ 
                                     ⌜v = #(n+1)⌝ ∗ own γ1 F ∨ 
                                     ⌜v = #(n+2)⌝ ∗ own γ1 F) ∗ own γ2 (1 / 3)%Qp)%I with "[Own1/3]")).
   { (* The first triple about the result of !ℓ *)
     (* We now open the invariant and destruct it into its three cases, one for each
        of the states. In each case, we close the invariant again with the same
        resources we got from opening it. *)
     iInv N as ">[I | [I | [I | I]]]" "Iclose".
     - (* Case 1: l ↦ #n ∗ own γ1 S *)
       iDestruct "I" as "[Hl  OwnS]".
       wp_load.
       (* To close the invariant in the same state, we provide the two resources again
          and use them to show the disjunct corresponding to that state. *)
       iMod ("Iclose" with "[Hl OwnS]") as "_".
       { iLeft. iFrame. }
       iFrame. iLeft. done.
     - (* Case 2: l ↦ #(n + 1) ∗ own γ1 F ∗ own γ2 (1 / 3)%Qp *)
       (* This is analogous to the first case. *)
       iDestruct "I" as "(Hl & OwnF & Own1/3_I)".
       (* We have to duplicate F, to have one to close the invariant and one for the
       postcondition. *)
       iDestruct (own_SFRA_FF with "OwnF") as "[OwnF_1 OwnF_2]".
       wp_load.
       iMod ("Iclose" with "[Hl OwnF_1 Own1/3_I]") as "_".
       { iRight. iLeft. iFrame. }
       iFrame. iRight. iFrame. iLeft. done.
       - (* Case 3: l ↦ #(n + 2) ∗ own γ1 F ∗ own γ2 (2 / 3)%Qp *)
       (* This is analogous to the first case. *)
       iDestruct "I" as "(Hl & OwnF & Own2/3_I)".
       (* We have to duplicate F, to have one to close the invariant and one for the
       postcondition. *)
       iDestruct (own_SFRA_FF with "OwnF") as "[OwnF_1 OwnF_2]".
       wp_load.
       iMod ("Iclose" with "[Hl OwnF_1 Own2/3_I]") as "_".
       { iNext. unfold incr_inv. iRight. iRight. iLeft. iFrame. } iModIntro.
       iFrame. iRight. iFrame. iRight. done.
     - (* Case 4: l ↦ #(n + 3) ∗ own γ1 F ∗ own γ2 1%Qp
          This state is impossible, as it means we have already incremented twice, represented by
          the ownership of 1. In this thread we have not come to writing to l yet (represented by
          still owning 1/3, which we would lose when closing the invariant in a new state ),
          l could thus have at most been updated once (by the other thread). We get the contradiction
          by combining the 1 from the invariant with the 1/3 of this thread into the invalid element (1 + 1/3). *)
       iDestruct "I" as "(Hl & OwnF & Own1)".
       iCombine "Own1 Own1/3" as "Own4/3".
       iDestruct (own_valid with "Own4/3") as "%Hinvalid".
       contradiction.
   }
   { (* The second triple about storing the incremented v *)
     iIntros (v) "[Hv Own1/3]".
     (* We consider the three cases for the value of v *)
     iDestruct "Hv" as "[-> | [[-> OwnF] | [-> OwnF]]]".
       wp_binop;
       (* To store the updated value, we again have to open the invariant. As before,
          we have to consider the different possible states the invariant can be in.
          Note that the state can have changed since we closed the invariant after
          reading, due to the other thread updating the value. Together with the 3
          possible values for v, we get 12 subgoals. *)
       iInv N as ">[I | [I | [I | I]]]" "Iclose";
       (* For case 4 of the invariant (ℓ ↦ #(n + 3) ∗ own γ1 F ∗ own γ2
          1%Qp) is impossible, as we could not have updated l thrice yet. Thus we
          solve the 3 corresponding subgoals with the contradiction obtained by
          combining 1 and 1/3, as before. *)
       try (
           iDestruct "I" as "(Hl & OwnF_I & Own1)";
           iCombine "Own1 Own1/3" as "Own4/3";
           iDestruct (own_valid with "Own4/3") as "%Hinvalid";
           contradiction
       );
       (* In the remaining cases, we store the updated value, and close the invariant
          in the corresponding state, depending on whether we stored n+1 or n+2 or
          n+3. To update the invariant's state, we have to transfer the 1/3 that was
          given to this thread into the invariant. *)
       iDestruct "I" as "[Hl Own]";
       wp_store; 
       try (replace (n+1+1)%Z with (n+2)%Z by lia);
       try (replace (n+2+1)%Z with (n+3)%Z by lia).
     - (* Case Storing (n + 1), invariant was in state S *)
       (* We have to show the second disjunct of the invariant to close it, which in
          addition to the 1/3 requires an F token. As the invariant was in the S
          state before, we have to update S to F. *)
       iMod (own_update _ _ F with "Own") as "OwnF"; first (apply SFRA_update).
       (* We then duplicate F, because we need to pass one F to the conclusion too. *)
       iDestruct (own_SFRA_FF with "OwnF") as "[OwnF_1 OwnF_2]".
       iMod ("Iclose" with "[Hl OwnF_1 Own1/3]") as "_".
       { iRight. iLeft. iFrame. }
       iApply ("Post" with "OwnF_2").
  
     - (* Case Storing (n + 1), invariant was in state F 1/3 *)
       (* 2nd Dijsunct. Another thread has incremented before us and contributed a 1/3
          token. The second disjunct is supposed to be true so we do not add our 1/3.
          We still have to duplicate the F token though, to be able to remember that
          the invariant is in a final state. *)
       iDestruct "Own" as "[OwnF Own1/3_I]".
       iDestruct (own_SFRA_FF with "OwnF") as "[OwnF_1 OwnF_2]".
       iMod ("Iclose" with "[Hl OwnF_1 Own1/3_I]") as "_".
       { iRight. iLeft. iFrame. }
       iApply ("Post" with "OwnF_2").
     - (* Case storing (n + 1), invariant was in state F 2/3 *)
       (* 2nd Disjunct. Two other threads have increment after we read the state. But
       we rewrite it to n + 1. So we replace the 2/3 token with our contribution.*)
     iDestruct "Own" as "[OwnF Own2/3_I]".
     iDestruct (own_SFRA_FF with "OwnF") as "[OwnF_1 OwnF_2]".
     iMod ("Iclose" with "[Hl OwnF_1 Own1/3]") as "_".
     { iRight. iLeft. iFrame. }
     iApply ("Post" with "OwnF_2").
     - (* Case storing (n + 2), invariant was in state S *)
       (* Impossible case *)
       iDestruct (own_SF_false with "[$Own $OwnF]") as "HFalse".
       done.
       - (* Case storing (n + 2), invariant was in state F 1/3 *)
       (* 3rd dijunct. We add our token to the invariant. *)
       iDestruct "Own" as "(OwnF_I & Own1/3_I)".
       iCombine "Own1/3 Own1/3_I" as "Own2/3".
       rewrite  div_2_3.
        iMod ("Iclose" with "[Hl OwnF_I Own2/3]") as "_".
       { iNext. iRight. iRight. iFrame. iLeft. iFrame. }
       iApply ("Post" with "OwnF"). 
    - (* Storing (n + 2), invariant was in state F 2/3 *)
       (* 3rd disjunct. Two threads have already contributed 1/3 tokens each. we do
          not contribute our token to the invariant. *)
          iDestruct "Own" as "(OwnF_I & Own2/3_I)".
          iMod ("Iclose" with "[Hl OwnF_I Own2/3_I]") as "_"; iFrame.
          { iNext. iRight. iRight. iLeft. iFrame. }
          iApply ("Post" with "OwnF").
    - (* Storing (n + 3), invariant was in state S *)
      (* Impossible case *)
      iDestruct (own_SF_false with "[$Own $OwnF]") as "HFalse".
      done.
    - (* Storing (n + 3), invariant was in state F 1/3 *)
      (* Impossible. *)
      iDestruct "Own" as "(OwnF_I & Own1/3_I)".
      iCombine "Own1/3 Own1/3_I" as "Own2/3".
      rewrite div_2_3.
      iMod ("Iclose" with "[Hl OwnF_I Own2/3]") as "_".
      { iRight. iRight. iFrame. iNext. }
      iApply ("Post" with "OwnF").
    - (* Storing (n + 3), invariant was in state F 2/3 *)
      (* This case represents the situation where two threads have run
          sequentially. Having stored n+2, we have to show the third disjunct of the
          invariant, which requires us to transfer an additional 1/3 to the invariant
          to obtain the required 1. *)
          iDestruct "Own" as "(OwnF_I & Own2/3_I)".
          iCombine "Own1/3 Own2/3_I" as "Own1".
          iMod ("Iclose" with "[Hl OwnF_I Own1]") as "_".
          { iRight. iRight. iFrame. }
          iApply ("Post" with "OwnF").

   }
 Qed.
 
 (* The actual specification for the whole program.
    Here we make use of the specification for a single thread we proved above. *)
 Lemma parallel_incr_spec (ℓ : loc) (n : Z):
   {{{ ℓ ↦ #n }}} (incr ℓ) ||| (incr ℓ) ;; !#ℓ {{{v, RET #v; ⌜(v = n+1)%Z⌝ ∨ ⌜(v = n+2)%Z⌝ }}}.
 Proof using Type* N.
   iIntros (Φ) "Hℓ Post".
   (* We start by allocating the start token S and the fraction 1. *)
   iMod (own_alloc S) as (γ1) "OwnS"; first done.
   iMod (own_alloc 1%Qp) as (γ2) "Own1"; first done.
   (* We allocate the invariant in the first state, where we have to provide an S
   token. *)
   iMod (inv_alloc N _ (incr_inv ℓ γ1 γ2 n) with "[Hℓ OwnS]") as "#Inv".
   { iLeft. iFrame. }
   (* We continue by focusing on the main part of the program, the parallel increment. *)
   wp_bind (_ ||| _)%E.
   (* For proving a conclusion for each thread, we want to pass a 1/2 fraction to
      each. Therefore we have to split the 1 we have into two halves. As frac is a
      fractional type, iDestruct can split the resource into two equal parts. *)
   - iDestruct "Own1" as "[Own1/2_1 Own1/2_2]".
     (* We now apply the par rule, passing one of the 1/2 to each thread. The
        arguments are the conclusions of the threads, which (according to our
        incr_spec) in both cases we choose to be the ownership of the F token. This
        will allow us to conclude that when the program terminates, the invariant
        must be in one of the F states (as S is incompatible with F). *)
     wp_smart_apply (wp_par (λ _ , own γ1 F)%I (λ _ , own γ1 F)%I with "[Own1/2_1] [Own1/2_2]").
     (* We can now for each thread apply our incr_spec specification. *)
     + iApply (incr_spec ℓ n γ1 γ2 with "[Inv Own1/2_1]"); first by iFrame.
       iNext. iIntros (_) "H". done.
     + iApply (incr_spec ℓ n γ1 γ2 with "[Inv Own1/2_2]"); first by iFrame.
       iNext. iIntros (_) "H". done.
     + (* As the final part, we have to show the second triple for reading the location,
          making use of the conclusions we get from both threads. *)
       iIntros (v1 v2) "OwnF".
       (* We get an F token from both threads, each stating that after the execution
          of one thread, the invariant must be in one of the final statse. *)
       iDestruct "OwnF" as "[OwnF _]".
       iNext.
       wp_pures.
       (* To read the location, we have to open the invariant again. We get three
          cases corresponding to the disjuncts in the invariant. As we have the F
          token, only the final states are possible cases, as we will see next. As we
          are only reading, as before we close the invariant again with the same
          resources we got from opening it. *)
       iInv N as ">[I | [I | I]]" "Iclose";
       iDestruct "I" as "[Hℓ Own]".
       * (* Case 1: ℓ ↦ #n, S
            This state is not possible as both threads either store n+1 or n+2 in ℓ.
            This is reflected by the incompatibility of owning the S token and an F token.
            To obtain a contradiction, we combine the S and F tokens as before. *)
         iDestruct (own_SF_false with "[$Own $OwnF]") as "HFalse".
         done.
       * (* Case 2: ℓ ↦ #(n + 1), F 1/2
            This state corresponds to the situation where only one thread
            has actually incremented the value. *)
         wp_load.
         (* As we only read the value stored at ℓ, we can close the invariant again
            with the same resources we got from opening. *)
         iMod ("Iclose" with "[Hℓ Own]") as "_".
         { iRight. iLeft. iFrame. }
         iModIntro. iApply "Post". iLeft. done.
       * (* Case 3: ℓ ↦ #(n + 2), F 1
            This state corresponds to the situation where both threads have
            incremented the value subsequently. *)
         wp_load.
         iMod ("Iclose" with "[Hℓ Own]") as "_".
         { iRight. iRight. iFrame. }
         iModIntro. iApply "Post". iRight. done.
 Qed.
 
 End proof.

 