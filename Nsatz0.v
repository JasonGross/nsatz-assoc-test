Require Export NsatzTest.Setup.
Definition pre_goal1 : goal1 * Prop.
  start.
  cbv delta [goal1].
  intros *.

  Ltac nsatz0 r0 :=
    let radicalmax := constr:(6%N) in
    let info := constr:(1%Z) in
    let lparam := constr:(@nil Q) in
    let lvar := constr:(@nil Q) in
    let nparam := eval compute in (Z.of_nat (List.length lparam)) in
        match goal with
          |- ?g => let lb := lterm_goal g in
                 let k := match lvar with
                          |(@nil _) =>
                           match lparam with
                           |(@nil _) =>
                            let r := constr:(list_reifyl (lterm:=lb)) in r
                           end end in pose k as r0 end.
  Time nsatz0 r0.
  finish.
Defined.

Definition goal1 : Prop.
Proof. get_snd pre_goal1. Defined.
