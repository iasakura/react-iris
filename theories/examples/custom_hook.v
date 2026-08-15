(** * A custom hook, specified once and used modularly.

<<
let Comp x =
  let useCounter = fun init ->
    let (c, setC) = useState init in
    fun sel -> if sel then c else (fun _ -> setC (fun v -> v + 1)) in
  let r = useCounter x in
  let (t, setT) = useState 0 in
  [r true; t; r false; fun _ -> setT (fun v -> v + 10)]
>>

    [useCounter] is an ordinary function containing a hook (there are no
    tuples in the language, so it returns a selector closure: [r true] is
    the count, [r false] the increment handler). Under cursor semantics
    (D2) it takes the slot at the cursor of the render in which it is
    called — slot 0 here — and the component's own [useState] the next
    one.

    The hook is specified once, in Init and Succ phase
    ([useCounter_init], [useCounter_succ]): from the render context, it
    consumes one slot at the cursor and returns its selector closure,
    with the count bound to the slot's (folded) value. The component body
    specifications ([comp_init], [comp_succ]) are then proved *from these
    specifications alone*, without unfolding the hook's body — the module
    discipline of design.md §5.3 (the slot count is exposed as [S (vw_cur
    π)]; hiding it behind an abstract hook context is future work). *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax domains interp machine.
From react_iris.logic Require Import inst lifting step_rules runtime_rules hooks runtime.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import proofmode.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Definition useCounter_body : syntax.expr :=
  EUseState 0 "c" "setC" (EVar "init")
    (EFun "sel"
       (EIf (EVar "sel") (EVar "c")
          (EFun "_" (EApp (EVar "setC")
                       (EFun "v" (EBop BPlus (EVar "v") (EConst (CInt 1)))))))).

Definition comp_body : syntax.expr :=
  ELet "useCounter" (EFun "init" useCounter_body)
    (ELet "r" (EApp (EVar "useCounter") (EVar "x"))
      (EUseState 0 "t" "setT" (EConst (CInt 0))
        (EView [EApp (EVar "r") (EConst (CBool true));
                EVar "t";
                EApp (EVar "r") (EConst (CBool false));
                EFun "_" (EApp (EVar "setT")
                            (EFun "v" (EBop BPlus (EVar "v") (EConst (CInt 10)))))]))).

Section custom_hook.
  Context `{!invGS Σ, !reactGS Σ}.
  Context (δ : def_table).

  Local Notation "'cint' n" := (VConst (CInt n)) (at level 10).

  (** The selector closure returned by the hook: count [c], slot [l] at
      path [p], defined in the environment [σ]. *)
  Definition counter_api (p : path) (l : label) (c : domains.val) (σ : env)
      : domains.val :=
    VClos "sel"
      (EIf (EVar "sel") (EVar "c")
         (EFun "_" (EApp (EVar "setC")
                      (EFun "v" (EBop BPlus (EVar "v") (EConst (CInt 1)))))))
      (env_insert "setC" (VSetter l p) (env_insert "c" c σ)).

  (** ** The hook's specifications (proved once) *)

  (** Init: allocate the slot at the cursor with the argument, return the
      API bound to it. *)
  Lemma useCounter_init (v : domains.val) σ p π ks Φ :
    render_ctx p π -∗
    (render_ctx p (π <| vw_sttst ::= insert (vw_cur π) (StEntry v []) |>
                     <| vw_cur := S (vw_cur π) |>) -∗
     WP ((FVal (counter_api p (vw_cur π) v (env_insert "init" v σ)), ks)
         : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FExpr PInit (env_insert "init" v σ) useCounter_body, ks)
        : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros "Hr Hwp". rewrite /useCounter_body.
    iApply (wp_usestate_init with "Hr"). iNext. iIntros "Hr".
    wp_pure.
    iApply (wp_usestate_mount with "Hr"). iNext. iIntros "Hr".
    wp_pure.
    by iApply "Hwp".
  Qed.

  (** Succ, pure queue: the count is the fold; the queue is flushed and
      Effect appears iff the count changed. *)
  Lemma useCounter_succ D (v : domains.val) σ p π v0 q fs ks Φ :
    vw_sttst π !! vw_cur π = Some (StEntry v0 q) →
    D v0 →
    queue_pure δ D q fs -∗
    render_ctx p π -∗
    (render_ctx p (commit_slot π (vw_cur π) v0 (fold_upd fs v0)) -∗
     WP ((FVal (counter_api p (vw_cur π) (fold_upd fs v0) (env_insert "init" v σ)), ks)
         : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FExpr PSucc (env_insert "init" v σ) useCounter_body, ks)
        : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hl HD) "#Hq Hr Hwp". rewrite /useCounter_body.
    iApply (wp_usestate_succ_pure with "Hq Hr"); [done|done|].
    iIntros "Hr". wp_pure.
    by iApply "Hwp".
  Qed.

  (** ** The component, from the hook's specifications only *)

  (** Init at argument [v]: the hook takes slot [vw_cur π] (0 on a fresh
      view), the component's state the next one; the view spec exposes
      the count, the component state, the increment handler, and the
      component's own handler. *)
  Lemma comp_init (v : domains.val) p π ks Φ :
    render_ctx p π -∗
    (let l := vw_cur π in
     let σr := env_insert "r" (counter_api p l v (env_insert "init" v [("x", v)]))
                 (env_insert "useCounter" (VClos "init" useCounter_body [("x", v)])
                    [("x", v)]) in
     render_ctx p (π <| vw_sttst ::= insert l (StEntry v []) |> <| vw_cur := S l |>
                     <| vw_sttst ::= insert (S l) (StEntry (cint 0) []) |>
                     <| vw_cur := S (S l) |>) -∗
     WP ((FVal (VList [v; cint 0;
                       VClos "_" (EApp (EVar "setC")
                                    (EFun "v" (EBop BPlus (EVar "v") (EConst (CInt 1)))))
                         (env_insert "sel" (VConst (CBool false))
                            (env_insert "setC" (VSetter l p)
                               (env_insert "c" v (env_insert "init" v [("x", v)]))));
                       VClos "_" (EApp (EVar "setT")
                                    (EFun "v" (EBop BPlus (EVar "v") (EConst (CInt 10)))))
                         (env_insert "setT" (VSetter (S l) p)
                            (env_insert "t" (cint 0) σr))]), ks)
         : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FExpr PInit [("x", v)] comp_body, ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros "Hr Hwp". rewrite /comp_body.
    (* let useCounter = ... in ...; the call [useCounter x] *)
    do 9 wp_pure.
    (* the hook, by its specification only *)
    iApply (useCounter_init with "Hr"). iIntros "Hr".
    (* let r = ...; the component's own useState *)
    wp_pure.
    iApply (wp_usestate_init with "Hr"). iNext. iIntros "Hr".
    wp_pure.
    iApply (wp_usestate_mount with "Hr"). iNext. iIntros "Hr".
    (* the view: r true, t, r false, handler *)
    do 25 wp_pure.
    iApply "Hwp". iExact "Hr".
  Qed.
End custom_hook.
