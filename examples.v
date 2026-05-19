Import Coq.Init.Nat.

Section Example.
  Check 0.
  Check S.
  Check nat.
  Print nat.
  Check Set.
  Check Type.
  Variable n : nat.
  Check n.
  Print n.
  Check n + 2.
  Check fun n => n + 2.
  Definition plus2 := fun (n : nat) => n + 2.
  Check plus2.
  Print plus2.
  Check 2 + 2.
  Compute 2 + 2.
  Check plus2 2.
  Compute plus2 2.
  Check n > 2.
  Check Prop.
  Definition myconj (A B : Prop) := forall (X : Prop), ((A -> B -> X) -> X).
  Check myconj.
  Definition myConjSet (A B : Set) := forall (X : Set), ((A -> B -> X) -> X).
  Check myConjSet.
  Compute n > 2.
  Check lt n 3.
  Check lt.
  Print lt.
  Check le.
  Print le.
  Compute 2 <= 3.
  Print bool.
  Fixpoint lefun (m n : nat) :=
     match n with
      | 0 => match m with
              | 0 => true
              | S m' => false
            end
      | S n' => match m with
                | 0 => true
                | S m' => lefun m' n'
               end
    end.
  Compute lefun 2 3.
  Compute lefun 3 2.
  Check 2 <? 3.
  Check lefun.
  Check le.
  Compute 2 <= 3.
  Lemma twole4 : 2 <= 4.
    auto.
  Qed.
  Check twole4.
  Print twole4.
  Print le.
End Example.

Section PropMinLog.
  Variable A : Prop.
  Goal A -> A.
    intro u.
    apply u.
    Show Proof.
  (* Qed. *)
  Save Identity.
  Check Identity.
  Print Identity.
  Definition IdentityTerm : A -> A := fun (u : A) => u.
  Check IdentityTerm.
  Print IdentityTerm.
  
  Variable B : Prop.
  Lemma K : A -> B -> A.
    intros u v.
    apply u.
  Qed.
  Print K.
  
  Definition KTerm : A -> B -> A := fun (u : A) (v : B) => u.
  Print KTerm.
  
  Variable C : Prop.
  Lemma S : (A -> B -> C) -> (A -> B) -> A -> C.
    intros u v w.
    apply u.
    apply w.
    apply v.
    apply w.
  Qed.

  Lemma S2 : (A -> B -> C) -> (A -> B) -> A -> C.
    intros u v w.
    apply u; [ assumption | apply v; assumption ].
  Qed.
  Print S.
  Print S2.

  Definition STerm : (A -> B -> C) -> (A -> B) -> A -> C := 
    fun u v w => u w (v w).
  Print STerm.
    
  Check and.
  Print and.
  Check and A B.
  Lemma ConjunctionIsCommutative : A /\ B -> B /\ A.
    intro u.
    split.
      apply u.
      apply u.
  Qed.
  
  Print ConjunctionIsCommutative.
  
  Print and_ind.
  
  Definition ConjunctionIsCommutativeTerm : A /\ B -> B /\ A :=
    fun u : A /\ B => conj
                   (match u with | conj v w => w end)
                   (match u with | conj v w => v end).
                   
  Print ConjunctionIsCommutativeTerm. 
  
  Check or.
  Print or.
  
  Lemma DisjunctionIsCommutative : A \/ B -> B \/ A.
    intro u.
    elim u.
      intro v.
      right.
      assumption.
      
      (* аналогично *)
      intro w.
      left.
      assumption.
  Qed.
  
  Print or_ind.
  
  Print DisjunctionIsCommutative.
  
End PropMinLog.
