(** * Adequacy: from WP to a pure statement about machine executions.

    [react_adequacy] closes the loop of M2: if, for any allocation of the
    ghost state, full ownership of the initial configuration entails a WP
    with a pure postcondition, then every machine execution from that
    configuration is safe — no Rules-of-React violation is reachable —
    and any reached value satisfies the postcondition.

    Mirrors heap_lang's adequacy setup: the state interpretation built by
    Iris's [wp_adequacy] is definitionally the one of [react_irisGS], so
    WPs proved against the latter apply. *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax domains interp machine.
From react_iris.logic Require Import inst lifting.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import proofmode.

Class reactGpreS (Σ : gFunctors) := ReactGpreS {
  react_pre_invGS :: invGpreS Σ;
  react_pre_mem :: ghost_mapG Σ path domains.view;
  react_pre_reg :: ghost_varG Σ (option (path * domains.view));
  react_pre_out :: ghost_varG Σ out_buf;
}.

Definition reactΣ : gFunctors :=
  #[invΣ; ghost_mapΣ path domains.view;
    ghost_varΣ (option (path * domains.view)); ghost_varΣ out_buf].

Global Instance subG_reactGpreS {Σ} : subG reactΣ Σ → reactGpreS Σ.
Proof. solve_inG. Qed.

Lemma react_alloc `{!reactGpreS Σ} c :
  ⊢ |==> ∃ _ : reactGS Σ, state_res (cfg_state c) ∗ own_cfg c.
Proof.
  iMod (ghost_map_alloc (mc_mem c)) as (γm) "[Hauth Hfrags]".
  iEval (rewrite -Qp.half_half
           (ghost_map_auth_fractional γm (mc_mem c)
              (1/2)%Qp (1/2)%Qp)) in "Hauth".
  iDestruct "Hauth" as "[Hauth Hauth']".
  iMod (ghost_var_alloc (mc_reg c)) as (γr) "Hreg".
  iEval (rewrite -Qp.half_half) in "Hreg".
  iDestruct (ghost_var_split with "Hreg") as "[Hreg Hreg']".
  iMod (ghost_var_alloc (mc_out c)) as (γo) "Hout".
  iEval (rewrite -Qp.half_half) in "Hout".
  iDestruct (ghost_var_split with "Hout") as "[Hout Hout']".
  iModIntro.
  iExists (ReactGS Σ _ _ _ γm γr γo).
  by iFrame.
Qed.

Theorem react_adequacy Σ `{!reactGpreS Σ} (δ : def_table) (c : mcfg)
    (φ : mval → Prop) :
  (∀ (HI : invGS Σ) (HR : reactGS Σ),
     own_cfg c ⊢ WP (cfg_expr c : expr (reactLang δ)) {{ w, ⌜φ w⌝ }}) →
  adequate NotStuck (cfg_expr c : expr (reactLang δ)) (cfg_state c)
    (λ w _, φ w).
Proof.
  intros Hwp.
  apply (wp_adequacy Σ (reactLang δ)).
  intros Hinv κs.
  iMod (react_alloc c) as (HR) "[Hsi Hown]".
  iModIntro.
  iExists (λ σ _, state_res σ), (λ _, True%I).
  iFrame "Hsi".
  by iApply Hwp.
Qed.
