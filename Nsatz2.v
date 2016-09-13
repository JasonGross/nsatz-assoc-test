Require Export NsatzTest.Nsatz1.
Definition pre_goal1 : goal1 * Prop.
  start.
  cbv delta [goal1].
  intros *.

  Ltac nsatz2 :=
    let radicalmax := constr:(6%N) in
    let info := constr:(1%Z) in
    let lparam := constr:(@nil Q) in
    let lvar := constr:(@nil Q) in
    let nparam := eval compute in (Z.of_nat (List.length lparam)) in
            match goal with
                   |- ?g =>
                       let lp := get_lpol g in
                       let lpol := eval compute in (List.rev lp) in
                       intros;

  let SplitPolyList kont :=
    match lpol with
    | ?p2::?lp2 => kont p2 lp2
    | _ => idtac "polynomial not in the ideal"
    end in

  SplitPolyList ltac:(fun p lp =>
    let p21 := fresh "p21" in
    let lp21 := fresh "lp21" in
    set (p21:=p) ;
    set (lp21:=lp);
(*    idtac "nparam:"; idtac nparam; idtac "p:"; idtac p; idtac "lp:"; idtac lp; *)
    nsatz_call radicalmax info nparam p lp ltac:(fun c r lq lci =>
      let q := fresh "q" in
      set (q := PEmul c (PEpow p21 r));
      let Hg := fresh "Hg" in
      assert (Hg:check lp21 q (lci,lq) = true);
      [ (vm_compute;reflexivity) || idtac "invalid nsatz certificate"
      | let Hg2 := fresh "Hg" in
            assert (Hg2: (interpret3 q fv) == 0);
        [ (*simpl*) idtac;
          generalize (@check_correct _ _ _ _ _ _ _ _ _ _ _ fv lp21 q (lci,lq) Hg);
          let cc := fresh "H" in
             (*simpl*) idtac; intro cc; apply cc; clear cc;
          (*simpl*) idtac;
          repeat (split;[assumption|idtac]); exact I
        | (*simpl in Hg2;*) (*simpl*) idtac;
          apply Rintegral_domain_pow with (interpret3 c fv) (N.to_nat r);
          (*simpl*) idtac;
            try apply integral_domain_one_zero;
            try apply integral_domain_minus_one_zero;
            try trivial;
            try exact integral_domain_one_zero;
            try exact integral_domain_minus_one_zero
          || (solve [simpl; unfold R2, equality, eq_notation, addition, add_notation,
                     one, one_notation, multiplication, mul_notation, zero, zero_notation;
                     discrR || omega])
          || ((*simpl*) idtac) || idtac "could not prove discrimination result"
        ]
      ]
)
                     ).
  Time nsatz2.
  finish.
Defined.

Definition goal1 : Prop.
Proof. get_snd pre_goal1. Defined.
