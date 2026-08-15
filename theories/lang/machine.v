(** * Small-step abstract machine for the React-tRace core calculus.

    Design decision D1: the runtime operations of the paper (init,
    reconcile, check, commitEffs, retrying evaluation, and the render-step
    loop) are internalized as machine expressions, yielding a single
    small-step transition system suitable for an Iris [language] instance.

    Shape: a CEK-style frame machine. A configuration holds
    - a focus (a source expression under evaluation, or a runtime
      operation, or an intermediate result being returned to the topmost
      frame),
    - a stack of continuation frames,
    - the tree memory,
    - the "render register": the view currently being rendered, if any
      (the paper's local-view context [π]; the path is bundled as in
      [rctx]), and
    - the output buffer.

    Deviation from the paper (behaviorally equivalent, checked by the
    cross-validation tests in [tests.v]): a component's view is written
    back to the tree memory as soon as its body evaluation completes,
    *before* its children are initialized/reconciled, so a single register
    suffices (no stack of in-progress views). The paper instead updates
    the memory at the end of each rule; no rule reads the parent's entry
    in between, so the final configurations agree.

    The machine is deterministic by construction ([mstep] is a function).
    User input enters as data, not as nondeterminism: the pending event
    trace sits at the bottom of the stack as a [KEvents] frame, and a
    quiescent focus dispatches the next index against the handlers of
    the rendered tree (STEPEVENT for a fixed trace). Top-level theorems
    quantify over the trace outside the logic, recovering the paper's
    adversarial user, while a fixed trace keeps the whole multi-event
    run a single execution — so ghost state flows through one WP. The
    quiescent focus [FIdle t] with an empty stack is the machine's value.

    A machine is stuck iff no rule applies, which coincides with the
    interpreter's [Stuck] (Rules-of-React violations). *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax domains interp.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

(** ** Foci and frames *)
Inductive focus :=
  (* Source-expression evaluation (paper: Σ, σ ⊢ e ⇓ᵠₚ …) *)
  | FExpr (φ : phase) (σ : env) (e : expr)
  | FVal (v : val)
  (* Run a component body with the retry loop (Fig. 6): enter the render
     register and evaluate. *)
  | FBody (φ : phase) (p : path) (π : view) (σ : env) (body : expr)
  (* Runtime operations on view specs and trees (Figs. 7–10) *)
  | FInit (s : val)
  | FRecon (t : tree) (s : val)
  | FCheck (t : tree)
  | FCommit (t : tree)
  (* Intermediate results returned to the topmost frame *)
  | FTree (t : tree)
  | FBool (b : bool)
  | FUnit
  (* Quiescent: event-loop mode • (a machine value) *)
  | FIdle (t : tree).

Inductive frame :=
  (* --- source-expression frames --- *)
  | KAppL (φ : phase) (σ : env) (e2 : expr)
  | KAppR (φ : phase) (v1 : val)
  | KIf (φ : phase) (σ : env) (e2 e3 : expr)
  | KLet (φ : phase) (σ : env) (x : var) (e2 : expr)
  | KSeq (φ : phase) (σ : env) (e2 : expr)
  | KView (φ : phase) (σ : env) (done : list val) (todo : list expr)
  | KUop (op : un_op)
  | KBopL (φ : phase) (σ : env) (op : bin_op) (e2 : expr)
  | KBopR (op : bin_op) (v1 : val)
  | KPrint
  (* useState, Init phase: after the initial value (STTBIND) *)
  | KUseState (σ : env) (l : label) (x xset : var) (e2 : expr)
  (* useState, Succ phase: folding the update queue (STTREBIND);
     [v0] is the committed value, [q] the remaining updaters *)
  | KSttFold (σ : env) (l : label) (x xset : var) (e2 : expr)
      (v0 : val) (q : list val)
  (* retry loop (EVALONCE/EVALMULT): restart the body while the round
     re-introduced the Check decision *)
  | KRetry (σ : env) (body : expr)
  (* --- init frames (Fig. 7) --- *)
  | KInitList (done : list tree) (todo : list val)
  | KInitBody (p : path)          (* body done: mount, init child spec *)
  | KInitChild (p : path)         (* child done: set dec:={Effect}, child *)
  (* --- reconcile frames (Fig. 10) --- *)
  | KReconList (done : list tree) (ttodo : list tree) (stodo : list val)
  | KReconBody (p : path) (child : tree)
  | KReconChild (p : path)
  (* --- check frames (Fig. 9) --- *)
  | KCheckList (b : bool) (todo : list tree)
  | KCheckBody (p : path) (child : tree)
  | KCheckRecon (p : path)        (* CHECKEFFECT: child reconciled *)
  (* --- commit frames (Fig. 8) --- *)
  | KCommitList (todo : list tree)
  | KCommitEffs (p : path) (q : list val)
  (* --- render-step loop (Fig. 4) --- *)
  | KMainInit                     (* main expression evaluated: init it *)
  | KMainMounted                  (* root tree built: enter rendered mode *)
  | KPostCommit (t : tree)        (* STEPEFFECT done: check *)
  | KPostCheck (t : tree)         (* STEPCHECK done: re-render or idle *)
  | KPostEvent (t : tree)         (* STEPEVENT done: check *)
  (* --- event driver ---
     The pending user-input trace. A quiescent focus dispatches the next
     index against the handlers of the rendered tree (STEPEVENT for a
     fixed trace); with the trace exhausted the frame pops and the
     machine reaches its value. Universally quantifying the trace
     outside the logic recovers the adversarial user of Fig. 4. *)
  | KEvents (evs : list nat).

(** ** Configurations *)
Record mcfg := MCfg {
  mc_focus : focus;
  mc_stack : list frame;
  mc_mem : tree_mem;
  mc_reg : option (path * view);   (* render register *)
  mc_out : out_buf;
}.

Global Instance mcfg_settable : Settable mcfg :=
  settable! MCfg <mc_focus; mc_stack; mc_mem; mc_reg; mc_out>.

Definition mcfg_value (c : mcfg) : option tree :=
  match mc_focus c, mc_stack c with
  | FIdle t, [] => Some t
  | _, _ => None
  end.

(** Handlers reachable in a rendered tree, in DFS order (the paper's
    [handlers(m, t)], with a fixed order so events address handlers by
    index). Structurally recursive on the tree; the fuel bounds only
    path indirections, so [S (map_size m)] hops suffice on any acyclic
    memory — a cycle (never reachable) surfaces as [Stuck]. Being total
    per call lets event dispatch be a single machine step. *)
Fixpoint handlers_h (hops : nat) (m : tree_mem) (t : tree)
    {struct hops} : res (list val) :=
  match hops with
  | O => Stuck "handlers: cyclic memory"
  | S h =>
      (fix go (t : tree) : res (list val) :=
         match t with
         | TConst _ => mret []
         | TClos x e σ => mret [VClos x e σ]
         | TList ts =>
             (fix gol (ts : list tree) : res (list val) :=
                match ts with
                | [] => mret []
                | t1 :: ts' =>
                    hs1 ← go t1; hs2 ← gol ts'; mret (hs1 ++ hs2)
                end) ts
         | TPath p =>
             match m !! p with
             | Some π => handlers_h h m (vw_child π)
             | None => Stuck "handlers: dangling path"
             end
         end) t
  end.

Definition handlers_of (m : tree_mem) (t : tree) : res (list val) :=
  handlers_h (S (map_size m)) m t.

(* Keep [handlers_of] opaque under simpl/cbn so that step-commutation
   proofs can split on its result ([vm_compute] is unaffected). *)
Global Arguments handlers_of : simpl never.

Section machine.
  Context (δ : def_table).

  (** Enter a component body: clear Check and the effect queue (each retry
      round does the same), load the render register, push the retry
      frame. *)
  Definition enter_body (φ : phase) (p : path) (π : view) (σ : env)
      (body : expr) (ks : list frame) (c : mcfg) : mcfg :=
    c <| mc_focus := FExpr φ σ body |>
      <| mc_stack := KRetry σ body :: ks |>
      <| mc_reg := Some (p, π <| vw_dec ::= dec_rm_check |> <| vw_effq := [] |>) |>.

  (** One machine step. [Stuck] means no rule applies; [OOF] is unused. *)
  Definition mstep (c : mcfg) : res mcfg :=
    match mc_focus c with
    (* ---------- source-expression dispatch ---------- *)
    | FExpr φ σ e =>
        match e with
        | EConst k => mret (c <| mc_focus := FVal (VConst k) |>)
        | EVar x =>
            match env_lookup x σ with
            | Some v => mret (c <| mc_focus := FVal v |>)
            | None => Stuck "unbound variable"
            end
        | ECompName C => mret (c <| mc_focus := FVal (VCompName C) |>)
        | EView [] => mret (c <| mc_focus := FVal (VList []) |>)
        | EView (e1 :: es) =>
            mret (c <| mc_focus := FExpr φ σ e1 |>
                    <| mc_stack ::= cons (KView φ σ [] es) |>)
        | EIf e1 e2 e3 =>
            mret (c <| mc_focus := FExpr φ σ e1 |>
                    <| mc_stack ::= cons (KIf φ σ e2 e3) |>)
        | EFun x e' => mret (c <| mc_focus := FVal (VClos x e' σ) |>)
        | EApp e1 e2 =>
            mret (c <| mc_focus := FExpr φ σ e1 |>
                    <| mc_stack ::= cons (KAppL φ σ e2) |>)
        | ELet x e1 e2 =>
            mret (c <| mc_focus := FExpr φ σ e1 |>
                    <| mc_stack ::= cons (KLet φ σ x e2) |>)
        | ESeq e1 e2 =>
            mret (c <| mc_focus := FExpr φ σ e1 |>
                    <| mc_stack ::= cons (KSeq φ σ e2) |>)
        | EUseState l x xset e1 e2 =>
            match φ, mc_reg c with
            | PInit, Some (_, _) =>
                (* STTBIND: evaluate the initial value first *)
                mret (c <| mc_focus := FExpr PInit σ e1 |>
                        <| mc_stack ::= cons (KUseState σ l x xset e2) |>)
            | PSucc, Some (p, π) =>
                (* STTREBIND: fold the queued updaters *)
                match vw_sttst π !! l with
                | None => Stuck "useState: unknown label"
                | Some (StEntry v0 q) =>
                    match q with
                    | [] =>
                        (* empty queue: value unchanged, no Effect *)
                        let π' := π <| vw_sttst ::= insert l (StEntry v0 []) |> in
                        let σ' := env_insert xset (VSetter l p)
                                    (env_insert x v0 σ) in
                        mret (c <| mc_focus := FExpr PSucc σ' e2 |>
                                <| mc_reg := Some (p, π') |>)
                    | VClos xi ei σi :: q' =>
                        mret (c <| mc_focus :=
                                     FExpr PSucc (env_insert xi v0 σi) ei |>
                                <| mc_stack ::=
                                     cons (KSttFold σ l x xset e2 v0 q') |>)
                    | _ :: _ => Stuck "useState: bad queue entry"
                    end
                end
            | _, _ => Stuck "useState: not in render phase"
            end
        | EUseEffect e' =>
            match φ, mc_reg c with
            | PInit, Some (p, π) | PSucc, Some (p, π) =>
                mret (c <| mc_focus := FVal (VConst CUnit) |>
                        <| mc_reg :=
                             Some (p, π <| vw_effq ::=
                                            (λ q, q ++ [VClos "_" e' σ]) |>) |>)
            | _, _ => Stuck "useEffect: not in render phase"
            end
        | EUop op e' =>
            mret (c <| mc_focus := FExpr φ σ e' |>
                    <| mc_stack ::= cons (KUop op) |>)
        | EBop op e1 e2 =>
            mret (c <| mc_focus := FExpr φ σ e1 |>
                    <| mc_stack ::= cons (KBopL φ σ op e2) |>)
        | EPrint e' =>
            mret (c <| mc_focus := FExpr φ σ e' |>
                    <| mc_stack ::= cons KPrint |>)
        end

    (* ---------- body entry ---------- *)
    | FBody φ p π σ body =>
        mret (enter_body φ p π σ body (mc_stack c) c)

    (* ---------- value return ---------- *)
    | FVal v =>
        match mc_stack c with
        | [] => Stuck "value with empty stack"
        | k :: ks =>
            let pop := c <| mc_stack := ks |> in
            match k with
            | KAppL φ σ e2 =>
                mret (pop <| mc_focus := FExpr φ σ e2 |>
                          <| mc_stack ::= cons (KAppR φ v) |>)
            | KAppR φ v1 =>
                match v1 with
                | VClos x eb σ' =>
                    (* APPFUNC *)
                    mret (pop <| mc_focus := FExpr φ (env_insert x v σ') eb |>)
                | VCompName C =>
                    (* APPCOM *)
                    mret (pop <| mc_focus := FVal (VCompSpec C v) |>)
                | VSetter l p' =>
                    match v with
                    | VClos _ _ _ =>
                        match φ, mc_reg pop with
                        | PInit, Some (p, π) | PSucc, Some (p, π) =>
                            (* APPSETCOMP: own setter only *)
                            if decide (p' = p) then
                              π' ← view_enqueue l v π;
                              mret (pop <| mc_focus := FVal (VConst CUnit) |>
                                        <| mc_reg := Some (p, π') |>)
                            else
                              Stuck "setter of another component during render"
                        | PNormal, None =>
                            (* APPSETNORMAL *)
                            match mc_mem pop !! p' with
                            | Some π =>
                                π' ← view_enqueue l v π;
                                mret (pop <| mc_focus := FVal (VConst CUnit) |>
                                          <| mc_mem ::= insert p' π' |>)
                            | None => Stuck "setter: dangling path"
                            end
                        | _, _ => Stuck "setter: phase/context mismatch"
                        end
                    | _ => Stuck "setter: updater must be a function"
                    end
                | _ => Stuck "app: not applicable"
                end
            | KIf φ σ e2 e3 =>
                match v with
                | VConst (CBool true) =>
                    mret (pop <| mc_focus := FExpr φ σ e2 |>)
                | VConst (CBool false) =>
                    mret (pop <| mc_focus := FExpr φ σ e3 |>)
                | _ => Stuck "if: bool expected"
                end
            | KLet φ σ x e2 =>
                mret (pop <| mc_focus := FExpr φ (env_insert x v σ) e2 |>)
            | KSeq φ σ e2 =>
                mret (pop <| mc_focus := FExpr φ σ e2 |>)
            | KView φ σ done todo =>
                match todo with
                | [] => mret (pop <| mc_focus := FVal (VList (done ++ [v])) |>)
                | e1 :: todo' =>
                    mret (pop <| mc_focus := FExpr φ σ e1 |>
                              <| mc_stack ::=
                                   cons (KView φ σ (done ++ [v]) todo') |>)
                end
            | KUop op =>
                r ← un_op_eval op v; mret (pop <| mc_focus := FVal r |>)
            | KBopL φ σ op e2 =>
                mret (pop <| mc_focus := FExpr φ σ e2 |>
                          <| mc_stack ::= cons (KBopR op v) |>)
            | KBopR op v1 =>
                r ← bin_op_eval op v1 v; mret (pop <| mc_focus := FVal r |>)
            | KPrint =>
                mret (pop <| mc_focus := FVal (VConst CUnit) |>
                          <| mc_out ::= (λ ω, ω ++ [v]) |>)
            | KUseState σ l x xset e2 =>
                (* STTBIND, after the initial value *)
                match mc_reg pop with
                | Some (p, π) =>
                    let π' := π <| vw_sttst ::= insert l (StEntry v []) |> in
                    let σ' := env_insert xset (VSetter l p)
                                (env_insert x v σ) in
                    mret (pop <| mc_focus := FExpr PInit σ' e2 |>
                              <| mc_reg := Some (p, π') |>)
                | None => Stuck "useState: no render register"
                end
            | KSttFold σ l x xset e2 v0 q =>
                (* STTREBIND, after one updater application *)
                match mc_reg pop with
                | Some (p, π) =>
                    match q with
                    | [] =>
                        let dec' := if val_eqb v v0 then vw_dec π
                                    else dec_add_effect (vw_dec π) in
                        let π' := π <| vw_dec := dec' |>
                                    <| vw_sttst ::= insert l (StEntry v []) |> in
                        let σ' := env_insert xset (VSetter l p)
                                    (env_insert x v σ) in
                        mret (pop <| mc_focus := FExpr PSucc σ' e2 |>
                                  <| mc_reg := Some (p, π') |>)
                    | VClos xi ei σi :: q' =>
                        mret (pop <| mc_focus :=
                                       FExpr PSucc (env_insert xi v σi) ei |>
                                  <| mc_stack ::=
                                       cons (KSttFold σ l x xset e2 v0 q') |>)
                    | _ :: _ => Stuck "useState: bad queue entry"
                    end
                | None => Stuck "useState: no render register"
                end
            | KRetry σ body =>
                (* EVALONCE / EVALMULT *)
                match mc_reg pop with
                | Some (p, π') =>
                    if dec_check (vw_dec π') then
                      mret (enter_body PSucc p π' σ body ks pop)
                    else
                      (* body settled: deliver the view spec to the frame
                         below (KInitBody / KReconBody / KCheckBody) *)
                      mret (pop <| mc_focus := FVal v |>)
                | None => Stuck "retry: no render register"
                end
            | KInitBody p =>
                (* INITCOM: mount the view, then initialize the child spec *)
                match mc_reg pop with
                | Some (p', π) =>
                    if decide (p' = p) then
                      mret (pop <| mc_focus := FInit v |>
                                <| mc_stack ::= cons (KInitChild p) |>
                                <| mc_mem ::= insert p π |>
                                <| mc_reg := None |>)
                    else Stuck "init: register mismatch"
                | None => Stuck "init: no render register"
                end
            | KReconBody p child =>
                (* RECONCILECOMEFFECT: write back, reconcile the old child *)
                match mc_reg pop with
                | Some (p', π') =>
                    if decide (p' = p) then
                      mret (pop <| mc_focus := FRecon child v |>
                                <| mc_stack ::= cons (KReconChild p) |>
                                <| mc_mem ::= insert p π' |>
                                <| mc_reg := None |>)
                    else Stuck "reconcile: register mismatch"
                | None => Stuck "reconcile: no render register"
                end
            | KCheckBody p child =>
                (* CHECKEFFECT / CHECKNOEFFECT: write back, then branch *)
                match mc_reg pop with
                | Some (p', π') =>
                    if decide (p' = p) then
                      let pop' := pop <| mc_mem ::= insert p π' |>
                                      <| mc_reg := None |> in
                      if dec_effect (vw_dec π') then
                        mret (pop' <| mc_focus := FRecon child v |>
                                   <| mc_stack ::= cons (KCheckRecon p) |>)
                      else
                        mret (pop' <| mc_focus := FCheck child |>)
                    else Stuck "check: register mismatch"
                | None => Stuck "check: no render register"
                end
            | KCommitEffs p q =>
                (* an effect body finished; run the rest *)
                match q with
                | [] =>
                    match mc_mem pop !! p with
                    | Some π =>
                        mret (pop <| mc_focus := FUnit |>
                                  <| mc_mem ::=
                                       insert p (π <| vw_dec ::= dec_rm_effect |>) |>)
                    | None => Stuck "commit: view vanished"
                    end
                | VClos _ e' σ' :: q' =>
                    mret (pop <| mc_focus := FExpr PNormal σ' e' |>
                              <| mc_stack ::= cons (KCommitEffs p q') |>)
                | _ :: _ => Stuck "commit: bad effect entry"
                end
            | KMainInit =>
                (* STEPINIT: the main expression produced a view spec *)
                mret (pop <| mc_focus := FInit v |>
                          <| mc_stack ::= cons KMainMounted |>)
            | KPostEvent t =>
                (* STEPEVENT done: enter check mode *)
                mret (pop <| mc_focus := FCheck t |>
                          <| mc_stack ::= cons (KPostCheck t) |>)
            | _ => Stuck "value: unexpected frame"
            end
        end

    (* ---------- init dispatch (Fig. 7) ---------- *)
    | FInit s =>
        match s with
        | VConst k => mret (c <| mc_focus := FTree (TConst k) |>)
        | VClos x e σ => mret (c <| mc_focus := FTree (TClos x e σ) |>)
        | VList [] => mret (c <| mc_focus := FTree (TList []) |>)
        | VList (s1 :: ss) =>
            mret (c <| mc_focus := FInit s1 |>
                    <| mc_stack ::= cons (KInitList [] ss) |>)
        | VCompSpec C v =>
            match δ !! C with
            | None => Stuck "undefined component"
            | Some (CompDef x body) =>
                let p := fresh_path (mc_mem c) in
                let π0 := MkView C v dec_empty ∅ [] (TConst CUnit) in
                mret (c <| mc_focus := FBody PInit p π0 [(x, v)] body |>
                        <| mc_stack ::= cons (KInitBody p) |>)
            end
        | _ => Stuck "init: not a view spec"
        end

    (* ---------- reconcile dispatch (Fig. 10) ---------- *)
    | FRecon t s =>
        match t, s with
        | TList ts, VList ss =>
            if decide (length ts = length ss) then
              match ts, ss with
              | [], [] => mret (c <| mc_focus := FTree (TList []) |>)
              | t1 :: ts', s1 :: ss' =>
                  mret (c <| mc_focus := FRecon t1 s1 |>
                          <| mc_stack ::= cons (KReconList [] ts' ss') |>)
              | _, _ => Stuck "reconcile: impossible"
              end
            else
              (* length mismatch: re-initialize (see interp.v) *)
              mret (c <| mc_focus := FInit s |>)
        | TPath p, VCompSpec C v =>
            match mc_mem c !! p with
            | None => Stuck "reconcile: dangling path"
            | Some π =>
                if decide (vw_comp π = C) then
                  match δ !! C with
                  | None => Stuck "undefined component"
                  | Some (CompDef x body) =>
                      mret (c <| mc_focus :=
                                   FBody PSucc p (π <| vw_arg := v |>)
                                     [(x, v)] body |>
                              <| mc_stack ::=
                                   cons (KReconBody p (vw_child π)) |>)
                  end
                else mret (c <| mc_focus := FInit s |>)  (* RECONCILECOMNEW *)
            end
        | _, _ => mret (c <| mc_focus := FInit s |>)     (* RECONCILEOTHER *)
        end

    (* ---------- check dispatch (Fig. 9) ---------- *)
    | FCheck t =>
        match t with
        | TConst _ | TClos _ _ _ => mret (c <| mc_focus := FBool false |>)
        | TList [] => mret (c <| mc_focus := FBool false |>)
        | TList (t1 :: ts) =>
            mret (c <| mc_focus := FCheck t1 |>
                    <| mc_stack ::= cons (KCheckList false ts) |>)
        | TPath p =>
            match mc_mem c !! p with
            | None => Stuck "check: dangling path"
            | Some π =>
                if dec_check (vw_dec π) then
                  match δ !! vw_comp π with
                  | None => Stuck "undefined component"
                  | Some (CompDef x body) =>
                      mret (c <| mc_focus :=
                                   FBody PSucc p π [(x, vw_arg π)] body |>
                              <| mc_stack ::=
                                   cons (KCheckBody p (vw_child π)) |>)
                  end
                else
                  (* CHECKIDLE: tail-recurse into the child *)
                  mret (c <| mc_focus := FCheck (vw_child π) |>)
            end
        end

    (* ---------- commit dispatch (Fig. 8) ---------- *)
    | FCommit t =>
        match t with
        | TConst _ | TClos _ _ _ => mret (c <| mc_focus := FUnit |>)
        | TList [] => mret (c <| mc_focus := FUnit |>)
        | TList (t1 :: ts) =>
            mret (c <| mc_focus := FCommit t1 |>
                    <| mc_stack ::= cons (KCommitList ts) |>)
        | TPath p =>
            match mc_mem c !! p with
            | None => Stuck "commit: dangling path"
            | Some π =>
                if dec_effect (vw_dec π) then
                  mret (c <| mc_focus := FCommit (vw_child π) |>
                          <| mc_stack ::= cons (KCommitEffs p (vw_effq π)) |>)
                else
                  (* COMMITEFFSPATHIDLE *)
                  mret (c <| mc_focus := FCommit (vw_child π) |>)
            end
        end

    (* ---------- tree return ---------- *)
    | FTree t =>
        match mc_stack c with
        | [] => Stuck "tree with empty stack"
        | k :: ks =>
            let pop := c <| mc_stack := ks |> in
            match k with
            | KInitList done todo =>
                match todo with
                | [] => mret (pop <| mc_focus := FTree (TList (done ++ [t])) |>)
                | s1 :: todo' =>
                    mret (pop <| mc_focus := FInit s1 |>
                              <| mc_stack ::=
                                   cons (KInitList (done ++ [t]) todo') |>)
                end
            | KInitChild p =>
                match mc_mem pop !! p with
                | Some π =>
                    mret (pop <| mc_focus := FTree (TPath p) |>
                              <| mc_mem ::=
                                   insert p (π <| vw_dec := Decisions false true |>
                                               <| vw_child := t |>) |>)
                | None => Stuck "init: view vanished"
                end
            | KReconList done ttodo stodo =>
                match ttodo, stodo with
                | [], [] =>
                    mret (pop <| mc_focus := FTree (TList (done ++ [t])) |>)
                | t1 :: tts, s1 :: sts =>
                    mret (pop <| mc_focus := FRecon t1 s1 |>
                              <| mc_stack ::=
                                   cons (KReconList (done ++ [t]) tts sts) |>)
                | _, _ => Stuck "reconcile: impossible"
                end
            | KReconChild p =>
                match mc_mem pop !! p with
                | Some π =>
                    mret (pop <| mc_focus := FTree (TPath p) |>
                              <| mc_mem ::=
                                   insert p (π <| vw_dec := Decisions false true |>
                                               <| vw_child := t |>) |>)
                | None => Stuck "reconcile: view vanished"
                end
            | KCheckRecon p =>
                (* CHECKEFFECT: install the reconciled child, report ❀ *)
                match mc_mem pop !! p with
                | Some π =>
                    mret (pop <| mc_focus := FBool true |>
                              <| mc_mem ::= insert p (π <| vw_child := t |>) |>)
                | None => Stuck "check: view vanished"
                end
            | KMainMounted =>
                (* STEPINIT done: rendered mode ❀ — commit effects *)
                mret (pop <| mc_focus := FCommit t |>
                          <| mc_stack ::= cons (KPostCommit t) |>)
            | _ => Stuck "tree: unexpected frame"
            end
        end

    (* ---------- boolean (check result) return ---------- *)
    | FBool b =>
        match mc_stack c with
        | [] => Stuck "bool with empty stack"
        | k :: ks =>
            let pop := c <| mc_stack := ks |> in
            match k with
            | KCheckList b0 todo =>
                match todo with
                | [] => mret (pop <| mc_focus := FBool (orb b0 b) |>)
                | t1 :: todo' =>
                    mret (pop <| mc_focus := FCheck t1 |>
                              <| mc_stack ::=
                                   cons (KCheckList (orb b0 b) todo') |>)
                end
            | KPostCheck t =>
                (* STEPCHECK done: ❀ → commit again; • → quiescent *)
                if b then
                  mret (pop <| mc_focus := FCommit t |>
                            <| mc_stack ::= cons (KPostCommit t) |>)
                else
                  mret (pop <| mc_focus := FIdle t |>)
            | _ => Stuck "bool: unexpected frame"
            end
        end

    (* ---------- unit (commit result) return ---------- *)
    | FUnit =>
        match mc_stack c with
        | [] => Stuck "unit with empty stack"
        | k :: ks =>
            let pop := c <| mc_stack := ks |> in
            match k with
            | KCommitList todo =>
                match todo with
                | [] => mret (pop <| mc_focus := FUnit |>)
                | t1 :: todo' =>
                    mret (pop <| mc_focus := FCommit t1 |>
                              <| mc_stack ::= cons (KCommitList todo') |>)
                end
            | KCommitEffs p q =>
                (* child effects committed: run this view's queue *)
                match q with
                | [] =>
                    match mc_mem pop !! p with
                    | Some π =>
                        mret (pop <| mc_focus := FUnit |>
                                  <| mc_mem ::=
                                       insert p (π <| vw_dec ::= dec_rm_effect |>) |>)
                    | None => Stuck "commit: view vanished"
                    end
                | VClos _ e' σ' :: q' =>
                    mret (pop <| mc_focus := FExpr PNormal σ' e' |>
                              <| mc_stack ::= cons (KCommitEffs p q') |>)
                | _ :: _ => Stuck "commit: bad effect entry"
                end
            | KPostCommit t =>
                (* STEPEFFECT done: check mode ↺ *)
                mret (pop <| mc_focus := FCheck t |>
                          <| mc_stack ::= cons (KPostCheck t) |>)
            | _ => Stuck "unit: unexpected frame"
            end
        end

    (* ---------- quiescent: event driver ---------- *)
    | FIdle t =>
        match mc_stack c with
        | KEvents [] :: ks =>
            (* trace exhausted: pop; with an empty stack this reaches
               the machine's value *)
            mret (c <| mc_stack := ks |>)
        | KEvents (i :: evs) :: ks =>
            (* STEPEVENT: dispatch the i-th handler of the rendered tree *)
            hs ← handlers_of (mc_mem c) t;
            match hs !! i with
            | Some (VClos x e σ) =>
                mret (c <| mc_focus :=
                             FExpr PNormal (env_insert x (VConst CUnit) σ) e |>
                        <| mc_stack := KPostEvent t :: KEvents evs :: ks |>)
            | _ => Stuck "event: no such handler"
            end
        | _ => Stuck "quiescent: waiting for an event"
        end
    end.

  (** Run until quiescent (or stuck / out of fuel). *)
  Fixpoint mrun (fuel : nat) (c : mcfg) : res mcfg :=
    match fuel with
    | O => OOF
    | S n =>
        match mcfg_value c with
        | Some _ => mret c
        | None => mstep c ≫= mrun n
        end
    end.

End machine.

(** ** Top-level runner (mirrors [run_prog])

    The whole run — mount plus the entire event trace — is one
    deterministic machine execution: the trace sits at the bottom of the
    stack as a [KEvents] frame. *)
Definition machine_init_cfg (P : prog) (evs : list nat) : mcfg :=
  MCfg (FExpr PNormal [] (p_main P)) [KMainInit; KEvents evs] ∅ None [].

Definition machine_run_prog (fuel : nat) (P : prog) (evs : list nat)
    : res mcfg :=
  mrun (prog_def_table P) fuel (machine_init_cfg P evs).

(** Machine and interpreter results projected to comparable data:
    quiescent tree, memory, and output. *)
Definition machine_result (fuel : nat) (P : prog) (evs : list nat)
    : res (tree * tree_mem * out_buf) :=
  machine_run_prog fuel P evs ≫= λ c,
  match mcfg_value c with
  | Some t => mret (t, mc_mem c, mc_out c)
  | None => Stuck "machine: not quiescent"
  end.

Definition interp_result (fuel : nat) (P : prog) (evs : list nat)
    : res (tree * tree_mem * out_buf) :=
  run_prog fuel P evs ≫= λ c, mret (c_tree c, c_mem c, c_out c).
