(** * Fueled executable interpreter for the React-tRace core calculus.

    Implements the big-step evaluation rules (Fig. 5 / App. A.2), retrying
    evaluation (Fig. 6), initialization (Fig. 7), effect commit (Fig. 8),
    check (Fig. 9), reconciliation (Fig. 10), and the render step
    transitions (Fig. 4) as fuel-indexed total functions.

    The interpreter is the executable reference for the small-step machine
    ([machine.v], to come): the react-trace test suite is ported against it
    ([tests.v]) so that distortions of the semantics are caught early
    (design decision D6).

    Results distinguish being stuck (no rule applies — a genuine error such
    as calling another component's setter during render) from running out
    of fuel (the paper's semantics is unbounded; infinite retry/re-render
    loops surface as [OOF]). *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax domains.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

(** ** Result monad *)
Inductive res (A : Type) : Type :=
  | Ok (a : A)
  | Stuck (msg : string)
  | OOF.
Arguments Ok {_} _.
Arguments Stuck {_} _.
Arguments OOF {_}.

Global Instance res_mret : MRet res := @Ok.
Global Instance res_mbind : MBind res := λ A B f r,
  match r with Ok a => f a | Stuck msg => Stuck msg | OOF => OOF end.
Global Instance res_fmap : FMap res := λ A B f r,
  match r with Ok a => Ok (f a) | Stuck msg => Stuck msg | OOF => OOF end.

Global Instance res_eq_dec `{EqDecision A} : EqDecision (res A).
Proof. solve_decision. Defined.

(** ** Primitive operators *)
Definition un_op_eval (op : un_op) (v : val) : res val :=
  match op, v with
  | UNeg, VConst (CInt n) => mret (VConst (CInt (Z.opp n)))
  | UNot, VConst (CBool b) => mret (VConst (CBool (negb b)))
  | _, _ => Stuck "un_op: type error"
  end.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : res val :=
  match op with
  | BEq => mret (VConst (CBool (val_eqb v1 v2)))
  | BNe => mret (VConst (CBool (negb (val_eqb v1 v2))))
  | BAnd =>
      match v1, v2 with
      | VConst (CBool b1), VConst (CBool b2) => mret (VConst (CBool (andb b1 b2)))
      | _, _ => Stuck "bin_op: bool expected"
      end
  | BOr =>
      match v1, v2 with
      | VConst (CBool b1), VConst (CBool b2) => mret (VConst (CBool (orb b1 b2)))
      | _, _ => Stuck "bin_op: bool expected"
      end
  | _ =>
      match v1, v2 with
      | VConst (CInt n1), VConst (CInt n2) =>
          match op with
          | BLt => mret (VConst (CBool (Z.ltb n1 n2)))
          | BGt => mret (VConst (CBool (Z.ltb n2 n1)))
          | BLe => mret (VConst (CBool (Z.leb n1 n2)))
          | BGe => mret (VConst (CBool (Z.leb n2 n1)))
          | BPlus => mret (VConst (CInt (Z.add n1 n2)))
          | BMinus => mret (VConst (CInt (Z.sub n1 n2)))
          | BTimes => mret (VConst (CInt (Z.mul n1 n2)))
          | BDiv => if decide (n2 = 0%Z) then Stuck "div by zero"
                    else mret (VConst (CInt (Z.div n1 n2)))
          | BMod => if decide (n2 = 0%Z) then Stuck "mod by zero"
                    else mret (VConst (CInt (Z.modulo n1 n2)))
          | _ => Stuck "bin_op: unreachable"
          end
      | _, _ => Stuck "bin_op: int expected"
      end
  end.

(** Fresh path allocation: strictly larger than every key of [m]
    (paper: [m ⊢ p fresh]; paths are never deallocated, so max+1 is fresh). *)
Definition fresh_path (m : tree_mem) : path :=
  map_fold (λ (p : path) (_ : view) (acc : path), S p `max` acc) 0%nat m.

Lemma fresh_path_spec (m : tree_mem) (p : path) (π : view) :
  m !! p = Some π → (p < fresh_path m)%nat.
Proof.
  revert p π. unfold fresh_path.
  apply (map_fold_weak_ind
           (λ acc mm, ∀ p π, mm !! p = Some π → (p < acc)%nat)).
  - intros p π ?. by simplify_map_eq.
  - intros i x mm r Hi IH p π. rewrite lookup_insert_Some.
    intros [[-> ->]|[Hne Hp]]; [lia|]. specialize (IH _ _ Hp). lia.
Qed.

Lemma fresh_path_fresh (m : tree_mem) : m !! fresh_path m = None.
Proof.
  destruct (m !! fresh_path m) as [π|] eqn:Hl; last done.
  pose proof (fresh_path_spec _ _ _ Hl). lia.
Qed.

(** Enqueue an update closure and set the Check decision on a view
    (the common effect of APPSETCOMP / APPSETNORMAL). *)
Definition view_enqueue (l : label) (cl : val) (π : view) : res view :=
  match vw_sttst π !! l with
  | None => Stuck "setter: unknown label"
  | Some ent =>
      mret (π <| vw_dec ::= dec_add_check |>
              <| vw_sttst ::=
                   insert l (ent <| st_queue ::= (λ q, q ++ [cl]) |>) |>)
  end.

Section interp.
  Context (δ : def_table).

  (** ** Expression evaluation (Fig. 5, App. A.2)

      [eval n φ Σ σ e = Ok (v, Σ', ω)] corresponds to
      [Σ, σ ⊢ e ⇓ᵠₚ v, Σ', ω], where the path subscript [p] is bundled
      into the view context ([RCtxView p π]). *)
  Fixpoint eval (fuel : nat) (φ : phase) (Σ : rctx) (σ : env) (e : expr)
      {struct fuel} : res (val * rctx * out_buf) :=
    match fuel with
    | O => OOF
    | S n =>
        match e with
        | EConst k => mret (VConst k, Σ, [])
        | EVar x =>
            match env_lookup x σ with
            | Some v => mret (v, Σ, [])
            | None => Stuck "unbound variable"
            end
        | ECompName C => mret (VCompName C, Σ, [])
        | EView es =>
            (fix go (es : list expr) (Σ : rctx)
                : res (list val * rctx * out_buf) :=
               match es with
               | [] => mret ([], Σ, [])
               | e :: es' =>
                   '(v, Σ1, ω1) ← eval n φ Σ σ e;
                   '(vs, Σ2, ω2) ← go es' Σ1;
                   mret (v :: vs, Σ2, ω1 ++ ω2)
               end) es Σ ≫= λ '(vs, Σ', ω), mret (VList vs, Σ', ω)
        | EIf e1 e2 e3 =>
            '(v1, Σ1, ω1) ← eval n φ Σ σ e1;
            match v1 with
            | VConst (CBool b) =>
                '(v, Σ2, ω2) ← eval n φ Σ1 σ (if b then e2 else e3);
                mret (v, Σ2, ω1 ++ ω2)
            | _ => Stuck "if: bool expected"
            end
        | EFun x e' => mret (VClos x e' σ, Σ, [])
        | EApp e1 e2 =>
            '(v1, Σ1, ω1) ← eval n φ Σ σ e1;
            '(v2, Σ2, ω2) ← eval n φ Σ1 σ e2;
            match v1 with
            | VClos x eb σ' =>
                (* APPFUNC *)
                '(v, Σ3, ω3) ← eval n φ Σ2 (env_insert x v2 σ') eb;
                mret (v, Σ3, ω1 ++ ω2 ++ ω3)
            | VCompName C =>
                (* APPCOM: package the component spec; the definition is
                   neither looked up nor invoked here. *)
                mret (VCompSpec C v2, Σ2, ω1 ++ ω2)
            | VSetter l p' =>
                match v2 with
                | VClos _ _ _ =>
                    match φ, Σ2 with
                    | PInit, RCtxView p π | PSucc, RCtxView p π =>
                        (* APPSETCOMP: during rendering, only the
                           component's own setter may be called. *)
                        if decide (p' = p) then
                          π' ← view_enqueue l v2 π;
                          mret (VConst CUnit, RCtxView p π', ω1 ++ ω2)
                        else Stuck "setter of another component during render"
                    | PNormal, RCtxMem m =>
                        (* APPSETNORMAL *)
                        match m !! p' with
                        | Some π =>
                            π' ← view_enqueue l v2 π;
                            mret (VConst CUnit, RCtxMem (<[p' := π']> m),
                                  ω1 ++ ω2)
                        | None => Stuck "setter: dangling path"
                        end
                    | _, _ => Stuck "setter: phase/context mismatch"
                    end
                | _ => Stuck "setter: updater must be a function"
                end
            | _ => Stuck "app: not applicable"
            end
        | ELet x e1 e2 =>
            '(v1, Σ1, ω1) ← eval n φ Σ σ e1;
            '(v2, Σ2, ω2) ← eval n φ Σ1 (env_insert x v1 σ) e2;
            mret (v2, Σ2, ω1 ++ ω2)
        | ESeq e1 e2 =>
            '(_, Σ1, ω1) ← eval n φ Σ σ e1;
            '(v2, Σ2, ω2) ← eval n φ Σ1 σ e2;
            mret (v2, Σ2, ω1 ++ ω2)
        | EUseState x xset e1 e2 =>
            (* Cursor semantics (D2): the slot is the hook's position among
               the render's hook calls ([vw_hook_cursor]); the syntactic label is
               ignored. *)
            match φ, Σ with
            | PInit, RCtxView p π =>
                (* STTBIND *)
                '(v1, Σ1, ω1) ← eval n PInit (RCtxView p π) σ e1;
                match Σ1 with
                | RCtxView p π1 =>
                    let l := vw_hook_cursor π1 in
                    let π2 := π1 <| vw_sttst ::= insert l (StEntry v1 []) |>
                                 <| vw_hook_cursor := S l |> in
                    let σ' := env_insert xset (VSetter l p)
                                (env_insert x v1 σ) in
                    '(v2, Σ2, ω2) ← eval n PInit (RCtxView p π2) σ' e2;
                    mret (v2, Σ2, ω1 ++ ω2)
                | _ => Stuck "useState: context changed"
                end
            | PSucc, RCtxView p π =>
                (* STTREBIND: fold the queued updaters over the committed
                   value; add the Effect decision iff the value changed. *)
                let l := vw_hook_cursor π in
                match vw_sttst π !! l with
                | None => Stuck "Rules of Hooks: more hooks than in the previous render"
                | Some (StEntry v0 q) =>
                    '(vn, Σ1, ω1) ←
                      (fix fold_q (q : list val) (v : val) (Σ : rctx)
                          : res (val * rctx * out_buf) :=
                         match q with
                         | [] => mret (v, Σ, [])
                         | VClos xi ei σi :: q' =>
                             '(vi, Σ1, ω1) ←
                               eval n PSucc Σ (env_insert xi v σi) ei;
                             '(vf, Σ2, ω2) ← fold_q q' vi Σ1;
                             mret (vf, Σ2, ω1 ++ ω2)
                         | _ :: _ => Stuck "useState: bad queue entry"
                         end) q v0 (RCtxView p π);
                    match Σ1 with
                    | RCtxView p πn =>
                        let dec' := if val_eqb vn v0 then vw_dec πn
                                    else dec_add_effect (vw_dec πn) in
                        let πn' := πn <| vw_dec := dec' |>
                                      <| vw_sttst ::= insert l (StEntry vn []) |>
                                      <| vw_hook_cursor := S l |> in
                        let σ' := env_insert xset (VSetter l p)
                                    (env_insert x vn σ) in
                        '(v2, Σ2, ω2) ← eval n PSucc (RCtxView p πn') σ' e2;
                        mret (v2, Σ2, ω1 ++ ω2)
                    | _ => Stuck "useState: context changed"
                    end
                end
            | _, _ => Stuck "useState: not in render phase"
            end
        | EUseEffect e' =>
            (* EFF: register the thunk; the binder-less thunk ⟨λ_.e, σ⟩ is
               represented as a closure whose body is evaluated directly in
               its stored environment at commit time (Fig. 8). *)
            match φ, Σ with
            | PInit, RCtxView p π | PSucc, RCtxView p π =>
                mret (VConst CUnit,
                      RCtxView p (π <| vw_effq ::= (λ q, q ++ [VClos "_" e' σ]) |>),
                      [])
            | _, _ => Stuck "useEffect: not in render phase"
            end
        | EUop op e' =>
            '(v, Σ1, ω1) ← eval n φ Σ σ e';
            r ← un_op_eval op v;
            mret (r, Σ1, ω1)
        | EBop op e1 e2 =>
            '(v1, Σ1, ω1) ← eval n φ Σ σ e1;
            '(v2, Σ2, ω2) ← eval n φ Σ1 σ e2;
            r ← bin_op_eval op v1 v2;
            mret (r, Σ2, ω1 ++ ω2)
        | EPrint e' =>
            '(v, Σ1, ω1) ← eval n φ Σ σ e';
            mret (VConst CUnit, Σ1, ω1 ++ [v])
        end
    end.

  (** ** Retrying evaluation of a component body (Fig. 6)

      Each round clears the effect queue and removes the Check decision;
      evaluation repeats (in Succ phase) while the round re-introduces
      Check. Divergence (the §3.1.2 pitfall) surfaces as [OOF]. *)
  Fixpoint eval_retry (fuel : nat) (φ : phase) (p : path) (π : view)
      (σ : env) (e : expr) {struct fuel} : res (val * view * out_buf) :=
    match fuel with
    | O => OOF
    | S n =>
        let π0 := π <| vw_dec ::= dec_rm_check |> <| vw_effq := [] |>
                    <| vw_hook_cursor := 0 |> in
        '(s, Σ', ω) ← eval n φ (RCtxView p π0) σ e;
        match Σ' with
        | RCtxView _ π' =>
            if dec_check (vw_dec π') then
              '(s', π'', ω') ← eval_retry n PSucc p π' σ e;
              mret (s', π'', ω ++ ω')
            else if decide (vw_hook_cursor π' = map_size (vw_sttst π'))
              then mret (s, π', ω)
              else Stuck "Rules of Hooks: fewer hooks than in the previous render"
        | _ => Stuck "retry: context changed"
        end
    end.

  (** Look up a component definition and run its body (shared by INITCOM,
      CHECK*, RECONCILECOMEFFECT). *)
  Definition eval_body (fuel : nat) (φ : phase) (p : path) (π : view)
      (arg : val) : res (val * view * out_buf) :=
    match δ !! vw_comp π with
    | None => Stuck "undefined component"
    | Some (CompDef x body) => eval_retry fuel φ p π [(x, arg)] body
    end.

  (** ** Initialization, reconciliation, and check
      (Figs. 7, 9, 10 — mutually recursive through the tree) *)
  Fixpoint init_vs (fuel : nat) (s : val) (m : tree_mem)
      {struct fuel} : res (tree * tree_mem * out_buf) :=
    match fuel with
    | O => OOF
    | S n =>
        match s with
        | VConst k => mret (TConst k, m, [])                     (* INITCONST *)
        | VClos x e σ => mret (TClos x e σ, m, [])               (* INITCLOS *)
        | VList ss =>                                            (* INITARRAY *)
            (fix go (ss : list val) (m : tree_mem)
                : res (list tree * tree_mem * out_buf) :=
               match ss with
               | [] => mret ([], m, [])
               | s :: ss' =>
                   '(t, m1, ω1) ← init_vs n s m;
                   '(ts, m2, ω2) ← go ss' m1;
                   mret (t :: ts, m2, ω1 ++ ω2)
               end) ss m ≫= λ '(ts, m', ω), mret (TList ts, m', ω)
        | VCompSpec C v =>                                       (* INITCOM *)
            let p := fresh_path m in
            let π0 := MkView C v dec_empty ∅ [] (TConst CUnit) 0 in
            '(s', π, ω) ← eval_body n PInit p π0 v;
            '(t, m', ω') ← init_vs n s' (<[p := π]> m);
            let πf := π <| vw_dec := Decisions false true |> <| vw_child := t |> in
            mret (TPath p, <[p := πf]> m', ω ++ ω')
        | _ => Stuck "init: not a view spec"
        end
    end

  with reconcile_t (fuel : nat) (t : tree) (s : val) (m : tree_mem)
      {struct fuel} : res (tree * tree_mem * out_buf) :=
    match fuel with
    | O => OOF
    | S n =>
        match t, s with
        | TList ts, VList ss =>                                  (* RECONCILEARRAY *)
            if decide (length ts = length ss) then
              (fix go (ts : list tree) (ss : list val) (m : tree_mem)
                  : res (list tree * tree_mem * out_buf) :=
                 match ts, ss with
                 | [], [] => mret ([], m, [])
                 | t :: ts', s :: ss' =>
                     '(t', m1, ω1) ← reconcile_t n t s m;
                     '(rs, m2, ω2) ← go ts' ss' m1;
                     mret (t' :: rs, m2, ω1 ++ ω2)
                 | _, _ => Stuck "reconcile: length mismatch"
                 end) ts ss m ≫= λ '(ts', m', ω), mret (TList ts', m', ω)
            else
              (* Length mismatch: not covered by the paper's rules; we
                 re-initialize like RECONCILEOTHER (TODO: cross-check
                 against the OCaml interpreter). *)
              init_vs n s m
        | TPath p, VCompSpec C v =>
            match m !! p with
            | None => Stuck "reconcile: dangling path"
            | Some π =>
                if decide (vw_comp π = C) then                   (* RECONCILECOMEFFECT *)
                  '(s', π', ω) ← eval_body n PSucc p (π <| vw_arg := v |>) v;
                  '(t', m', ω') ← reconcile_t n (vw_child π) s' m;
                  let πf := π' <| vw_dec := Decisions false true |>
                               <| vw_child := t' |> in
                  mret (TPath p, <[p := πf]> m', ω ++ ω')
                else init_vs n s m                               (* RECONCILECOMNEW *)
            end
        | _, _ => init_vs n s m                                  (* RECONCILEOTHER *)
        end
    end

  (** [check_t] returns [true] iff some component re-rendered
      (mode ❀ vs. •, joined with ⊔ across arrays). *)
  with check_t (fuel : nat) (t : tree) (m : tree_mem)
      {struct fuel} : res (bool * tree_mem * out_buf) :=
    match fuel with
    | O => OOF
    | S n =>
        match t with
        | TConst _ | TClos _ _ _ => mret (false, m, [])
        | TList ts =>                                            (* CHECKARRAY *)
            (fix go (ts : list tree) (m : tree_mem)
                : res (bool * tree_mem * out_buf) :=
               match ts with
               | [] => mret (false, m, [])
               | t :: ts' =>
                   '(b1, m1, ω1) ← check_t n t m;
                   '(b2, m2, ω2) ← go ts' m1;
                   mret (orb b1 b2, m2, ω1 ++ ω2)
               end) ts m
        | TPath p =>
            match m !! p with
            | None => Stuck "check: dangling path"
            | Some π =>
                if negb (dec_check (vw_dec π)) then              (* CHECKIDLE *)
                  check_t n (vw_child π) m
                else
                  '(s', π', ω) ← eval_body n PSucc p π (vw_arg π);
                  if dec_effect (vw_dec π') then                 (* CHECKEFFECT *)
                    '(t', m', ω') ← reconcile_t n (vw_child π) s' m;
                    mret (true, <[p := π' <| vw_child := t' |>]> m', ω ++ ω')
                  else                                           (* CHECKNOEFFECT *)
                    '(b, m', ω') ← check_t n (vw_child π) m;
                    mret (b, <[p := π']> m', ω ++ ω')
            end
        end
    end.

  (** ** Committing effects (Fig. 8): post-order; only views that decided
      to run Effects; each effect body runs in Normal phase over the whole
      memory. The effect queue is not cleared here — the next render round
      clears it (EVALONCE/EVALMULT). *)
  Fixpoint commit_t (fuel : nat) (t : tree) (m : tree_mem)
      {struct fuel} : res (tree_mem * out_buf) :=
    match fuel with
    | O => OOF
    | S n =>
        match t with
        | TConst _ | TClos _ _ _ => mret (m, [])
        | TList ts =>
            (fix go (ts : list tree) (m : tree_mem)
                : res (tree_mem * out_buf) :=
               match ts with
               | [] => mret (m, [])
               | t :: ts' =>
                   '(m1, ω1) ← commit_t n t m;
                   '(m2, ω2) ← go ts' m1;
                   mret (m2, ω1 ++ ω2)
               end) ts m
        | TPath p =>
            match m !! p with
            | None => Stuck "commit: dangling path"
            | Some π =>
                if negb (dec_effect (vw_dec π)) then             (* COMMITEFFSPATHIDLE *)
                  commit_t n (vw_child π) m
                else                                             (* COMMITEFFSPATH *)
                  '(m0, ω0) ← commit_t n (vw_child π) m;
                  '(mn, ωs) ←
                    (fix go (q : list val) (m : tree_mem)
                        : res (tree_mem * out_buf) :=
                       match q with
                       | [] => mret (m, [])
                       | VClos _ e σi :: q' =>
                           '(_, Σ', ωi) ← eval n PNormal (RCtxMem m) σi e;
                           match Σ' with
                           | RCtxMem mi =>
                               '(mf, ωf) ← go q' mi;
                               mret (mf, ωi ++ ωf)
                           | _ => Stuck "commit: context changed"
                           end
                       | _ :: _ => Stuck "commit: bad effect entry"
                       end) (vw_effq π) m0;
                  (* Re-read p: effects may have queued updates on it. *)
                  match mn !! p with
                  | None => Stuck "commit: view vanished"
                  | Some πn =>
                      mret (<[p := πn <| vw_dec ::= dec_rm_effect |>]> mn,
                            ω0 ++ ωs)
                  end
            end
        end
    end.

  (** ** Handlers reachable in the rendered tree (Fig. 4, STEPEVENT),
      in DFS order (the paper treats them as a set; we fix an order so
      that events can be addressed by index). *)
  Fixpoint handlers_t (fuel : nat) (m : tree_mem) (t : tree)
      {struct fuel} : res (list val) :=
    match fuel with
    | O => OOF
    | S n =>
        match t with
        | TConst _ => mret []
        | TClos x e σ => mret [VClos x e σ]
        | TList ts =>
            (fix go (ts : list tree) : res (list val) :=
               match ts with
               | [] => mret []
               | t :: ts' =>
                   hs1 ← handlers_t n m t;
                   hs2 ← go ts';
                   mret (hs1 ++ hs2)
               end) ts
        | TPath p =>
            match m !! p with
            | None => Stuck "handlers: dangling path"
            | Some π => handlers_t n m (vw_child π)
            end
        end
    end.

  (** ** The display: the realized view hierarchy in quiescent states
      (observation of D7; handlers are opaque).

      [display_tree f] is structurally recursive on the tree and defers
      every path to [f]; [display_h] plugs in the memory lookup and
      counts only path *hops*, so [S (map_size m)] of them suffice on
      any acyclic memory — a cycle (never reachable) surfaces as
      [Stuck]. Being total per call keeps the fuel out of theorem
      statements: they speak of [display m t], not of a numeral. *)
  Fixpoint display_tree (f : path → res dtree) (t : tree) {struct t} : res dtree :=
    match t with
    | TConst k => mret (DConst k)
    | TClos _ _ _ => mret DHandler
    | TList ts =>
        (fix go (ts : list tree) : res (list dtree) :=
           match ts with
           | [] => mret []
           | t1 :: ts' => d ← display_tree f t1; ds ← go ts'; mret (d :: ds)
           end) ts ≫= λ ds, mret (DList ds)
    | TPath p => f p
    end.

  Fixpoint display_h (hops : nat) (m : tree_mem) (t : tree)
      {struct hops} : res dtree :=
    match hops with
    | O => Stuck "display: cyclic memory"
    | S h =>
        display_tree
          (λ p, match m !! p with
                | None => Stuck "display: dangling path"
                | Some π => display_h h m (vw_child π)
                end) t
    end.

  Definition display (m : tree_mem) (t : tree) : res dtree :=
    display_h (S (map_size m)) m t.

  (** ** Render step transitions (Fig. 4) *)

  Definition step_init (fuel : nat) (e_main : expr) : res config :=
    '(s, _, ω) ← eval fuel PNormal (RCtxMem ∅) [] e_main;
    '(t, m, ω') ← init_vs fuel s ∅;
    mret (Config t m (ω ++ ω') MRendered).

  Definition step_effect (fuel : nat) (c : config) : res config :=
    '(m', ω) ← commit_t fuel (c_tree c) (c_mem c);
    mret (c <| c_mem := m' |> <| c_out ::= (λ ω0, ω0 ++ ω) |>
            <| c_mode := MCheck |>).

  Definition step_check (fuel : nat) (c : config) : res config :=
    '(b, m', ω) ← check_t fuel (c_tree c) (c_mem c);
    mret (c <| c_mem := m' |> <| c_out ::= (λ ω0, ω0 ++ ω) |>
            <| c_mode := (match b with true => MRendered | false => MEvent end) |>).

  Definition step_event (fuel : nat) (i : nat) (c : config) : res config :=
    hs ← handlers_t fuel (c_mem c) (c_tree c);
    match hs !! i with
    | Some (VClos x e σ) =>
        '(_, Σ', ω) ← eval fuel PNormal (RCtxMem (c_mem c))
                        (env_insert x (VConst CUnit) σ) e;
        match Σ' with
        | RCtxMem m' =>
            mret (c <| c_mem := m' |> <| c_out ::= (λ ω0, ω0 ++ ω) |>
                    <| c_mode := MCheck |>)
        | _ => Stuck "event: context changed"
        end
    | _ => Stuck "event: no such handler"
    end.

  (** Drive the render loop; in event-loop mode consume the next event
      index from [evs], stopping when no events remain. *)
  Fixpoint run_loop (fuel : nat) (c : config) (evs : list nat)
      {struct fuel} : res config :=
    match fuel with
    | O => OOF
    | S n =>
        match c_mode c with
        | MRendered => step_effect n c ≫= λ c', run_loop n c' evs
        | MCheck => step_check n c ≫= λ c', run_loop n c' evs
        | MEvent =>
            match evs with
            | [] => mret c
            | i :: evs' => step_event n i c ≫= λ c', run_loop n c' evs'
            end
        end
    end.

End interp.

(** ** Top-level runner *)
Definition run_prog (fuel : nat) (P : prog) (evs : list nat) : res config :=
  let δ := prog_def_table P in
  step_init δ fuel (p_main P) ≫= λ c, run_loop δ fuel c evs.

(** Convenience projections for tests. *)
Definition state_at (c : config) (p : path) (l : label) : option val :=
  match c_mem c !! p with
  | Some π => st_val <$> (vw_sttst π !! l)
  | None => None
  end.

Definition display_of (c : config) : res dtree :=
  display (c_mem c) (c_tree c).
