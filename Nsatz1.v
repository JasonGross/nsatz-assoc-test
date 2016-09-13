Require Export NsatzTest.Nsatz0.
Definition pre_goal1 : goal1 * Prop.
  start.
  cbv delta [goal1].
  intros *.

  Ltac nsatz1 :=
    let radicalmax := constr:(6%N) in
    let info := constr:(1%Z) in
    let lparam := constr:(@nil Q) in
    let lvar := constr:(@nil Q) in
    let nparam := eval compute in (Z.of_nat (List.length lparam)) in
        let r0 := fresh in
        intro r0;
        let r := (eval cbv delta [r0] in r0) in
        clear r0;
        lazymatch goal with
          |- ?g => let lb := lterm_goal g in
                 lazymatch eval red in r with
                 |(?fv, ?le) =>
                  reify_goal fv le lb
                 end
        end.
  Time nsatz1.
  finish.
Defined.

Definition goal1 : Prop.
Proof. get_snd pre_goal1. Defined.
