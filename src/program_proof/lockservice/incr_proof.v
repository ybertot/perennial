From Perennial.algebra Require Import auth_map.
From Perennial.program_proof Require Import proof_prelude marshal_proof.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Goose.github_com.mit_pdos.lockservice Require Import lockservice.
From Perennial.program_proof.lockservice Require Import rpc_proof rpc nondet kv_proof fmcounter_map wpc_proofmode common_proof.
Require Import Decimal Ascii String DecimalString.
From Perennial.goose_lang Require Import ffi.grove_ffi.

Section rpc_proof.
Context `{!heapG Σ}.
Context `{!rpcG Σ u64}.

(* This is the fupd that the server uses to get the (PreCond ∨ PostCond) of an old request after increasing seqno to quiesce it *)
Definition quiesce_fupd γrpc (cid seq:u64) (PreCond : RPCValC → iProp Σ) (PostCond:RPCValC → u64 → iProp Σ) : (RPCValC → iProp Σ) :=
  λ (args:RPCValC),
        (own γrpc.(proc) (Excl ()) -∗ cid fm[[γrpc.(lseq)]]≥ int.nat seq ={⊤}=∗ own γrpc.(proc) (Excl ()) ∗ ▷ (PreCond args ∨ (∃ reply,PostCond args reply)))%I.

(* TODO: Want a quiesce_fupd that gives a user-chosen resource so long as one provides a proof that (PreCond ∨ PostCond ={⊤}=∗ user-chosen-resource) *)
(* E.g. if we want to do a new Put() after giving up on a Get(), we should be able to quiesce the Get() and  *)

(* This gives the quiesce_fupd for any sequence number that the client can take on
   This is the precondition for ck.MakeRequest(args), where ck has the given cid *)
Definition quiesceable_pre γrpc cid args PreCond PostCond : iProp Σ :=
    <bdisc> (∀ seq, cid fm[[γrpc.(cseq)]]↦ int.nat seq ={⊤}=∗
      cid fm[[γrpc.(cseq)]]↦ int.nat seq ∗
   quiesce_fupd γrpc cid seq PreCond PostCond args)
.

Definition own_rpcclient (cl_ptr:loc) (γrpc:rpc_names) (cid:u64) : iProp Σ
  :=
    ∃ (cseqno:u64),
      "%" ∷ ⌜int.nat cseqno > 0⌝
    ∗ "Hcid" ∷ cl_ptr ↦[RPCClient.S :: "cid"] #cid
    ∗ "Hseq" ∷ cl_ptr ↦[RPCClient.S :: "seq"] #cseqno
    ∗ "Hcrpc" ∷ RPCClient_own γrpc cid cseqno
.

Theorem wpc_forBreak_cond' (P: iProp Σ) stk k E (cond body: goose_lang.val) (Φ : goose_lang.val → iProp Σ) (Φc: iProp Σ) :
  P -∗
  (P -∗ <disc> Φc) -∗
  □ (P -∗
      WPC if: cond #() then body #() else #false @ stk; k; E
      {{ v, ⌜v = #true⌝ ∗ P ∨ ⌜v = #false⌝ ∗ (Φ #() ∧ <disc> Φc) }} {{ Φc }} ) -∗
  WPC (for: cond; (λ: <>, Skip)%V := body) @ stk; k ; E {{ Φ }} {{ Φc }}.
Proof.
  iIntros "HP HΦc #Hbody".
  rewrite /For.
  iCache with "HP HΦc".
  { by iApply "HΦc". }
  wpc_pures.
  iLöb as "IH".
  wpc_bind_seq.
  iDestruct ("Hbody" with "HP") as "Hbody1".
  iApply (wpc_strong_mono with "Hbody1"); try auto.
  iSplit; last first.
  {
    iModIntro. iIntros.
    by iModIntro.
  }
  iIntros (v) "H".
  iModIntro.
  iDestruct "H" as "[[% H]|[% H]]"; subst.
  - iCache with "HΦc H".
    { iSpecialize ("HΦc" with "H"). done. }
    wpc_pures.
    wpc_pures.
    iApply ("IH" with "[$] [$]").
  - iCache with "H".
    { by iRight in "H". }
    wpc_pures.
    wpc_pures.
    by iLeft in "H".
Qed.

Lemma quiesce_request (req:RPCRequest) γrpc γreq PreCond PostCond :
  is_RPCServer γrpc -∗
  is_RPCRequest γrpc γreq PreCond PostCond req -∗
  (RPCRequest_token γreq) -∗
  quiesceable_pre γrpc req.(Req_CID) req.(Req_Args) PreCond PostCond.
Proof.
    iIntros "#Hsrpc #His_req Hγpost".
    (* iDestruct (fmcounter_map_get_lb with "Hcown") as "#Hcseq_lb". *)
    iModIntro.

    iIntros (new_seq) "Hcown".

    iInv "His_req" as "[>#Hcseq_lb_strict HN]" "HNClose".
    iMod ("HNClose" with "[$Hcseq_lb_strict $HN]") as "_".

    iDestruct (fmcounter_map_agree_lb with "Hcown Hcseq_lb_strict") as %Hnew_seq.
    iModIntro.
    iFrame.

    iIntros "Hγproc #Hlseq_lb".
    iInv "His_req" as "HN" "HNClose".
    iDestruct "HN" as "[#>_ [HN|HN]]"; simpl. (* Is cseq_lb_strict relevant for this? *)
    {
      iDestruct "HN" as "[_ [>Hbad|HN]]".
      { iDestruct (own_valid_2 with "Hbad Hγproc") as %?; contradiction. }

      iMod ("HNClose" with "[Hγpost]") as "_".
      { iNext. iFrame "Hcseq_lb_strict". iRight. iFrame.
        iDestruct (fmcounter_map_mono_lb (int.nat req.(Req_Seq)) with "Hlseq_lb") as "$".
        lia.
      }
      iFrame.
      iModIntro.
      iNext.
      iLeft.
      iDestruct "HN" as "[_ $]".
    }
    {
      iDestruct "HN" as "[#Hlseq_lb_req HN]".
      iDestruct "HN" as "[>Hbad|Hreply_post]".
      { by iDestruct (own_valid_2 with "Hγpost Hbad") as %Hbad. }
      iMod ("HNClose" with "[Hγpost]") as "_".
      {
        iNext.
        iFrame "Hcseq_lb_strict".
        iRight.
        iFrame "# ∗".
      }
      iDestruct "Hreply_post" as (last_reply) "[#Hreply Hpost]".
      iModIntro.
      iFrame.
      iRight.
      iExists _; iFrame.
    }
Qed.

(* Need to have the fmcounter fact because the quiesce_fupd in the
   quiesceable_pre is specialized to a particular seqno, while we need to know
   that any seqno is good. The fmcounter fact is one way to get around this.
   Alternatively, could also maybe make the RPCRequestInvariant contain
   (quiesce_fupd ∧ quiesceable_pre).
 *)
Lemma quiesce_idemp_1 γrpc req seqno PreCond PostCond:
  req.(Req_CID) fm[[γrpc.(cseq)]]≥ int.nat seqno -∗
  quiesceable_pre γrpc req.(Req_CID) req.(Req_Args) (quiesce_fupd γrpc req.(Req_CID) seqno PreCond PostCond) PostCond -∗
  quiesceable_pre γrpc req.(Req_CID) req.(Req_Args) PreCond PostCond.
Proof.
  iIntros "#Hseqno_lb Hqfupd".
  iModIntro. iIntros (seq) "Hcown".
  iDestruct (fmcounter_map_agree_lb with "Hcown Hseqno_lb") as %Hseqno_ineq.

  iDestruct ("Hqfupd" $! seq with "Hcown") as ">[$ Hqfupd]".
  iModIntro.

  iIntros "Hγproc #Hlb".
  iDestruct ("Hqfupd" with "Hγproc Hlb") as ">[Hγproc [Hqfupd|Hreply]]".
  {
    iAssert (quiesce_fupd γrpc req.(Req_CID) seqno PreCond PostCond req.(Req_Args))%I with "[Hqfupd]" as "Hqfupd".
    { admit. } (* Need PreCond to be timeless for this to work out; too many laters *)
    iSpecialize ("Hqfupd" with "Hγproc").
    iDestruct (fmcounter_map_mono_lb (int.nat seqno) with "Hlb") as "#Hlseq_seqno_lb".
    { lia. }
    iSpecialize ("Hqfupd" with "Hlseq_seqno_lb").
    iFrame.
  }
  {
    iModIntro. iFrame.
  }
Admitted. (* timeless precond *)

Lemma quiesce_idemp_2 γrpc req seqno PreCond PostCond:
  quiesceable_pre γrpc req.(Req_CID) req.(Req_Args)
        (λ args, (quiesce_fupd γrpc req.(Req_CID) seqno PreCond PostCond args) ∧
           (quiesceable_pre γrpc req.(Req_CID) req.(Req_Args) PreCond PostCond)
           )
        PostCond -∗
  quiesceable_pre γrpc req.(Req_CID) req.(Req_Args) PreCond PostCond.
Proof.
  iIntros "Hqfupd".
  iModIntro. iIntros (seq) "Hcown".
  iDestruct (fmcounter_map_get_lb with "Hcown") as "#Hlb".

  iDestruct ("Hqfupd" $! seq with "Hcown") as ">[$ Hqfupd]".
  iModIntro.
  iIntros "Hγproc #Hlb2".
  (* TODO: this would work out if quiesceable_pre required only an fm[[...]]≥ fact as input; luckily, we can do that! *)
  (*
  iSpecialize ("Hqfupd" with "Hγproc Hlb2").

  iDestruct ("Hqfupd" with "Hγproc Hlb") as ">[Hγproc [Hqfupd|Hreply]]".
  {
    iRight in "Hqfupd".
  } *)
Admitted.

Lemma wpc_RPCClient__MakeRequest k (f:goose_lang.val) cl_ptr cid args γrpc (PreCond:RPCValC -> iProp Σ) PostCond {_:Discretizable (PreCond args)} {_:∀ reply, Discretizable (PostCond args reply)}:
  (∀ seqno, is_rpcHandler f γrpc (quiesce_fupd γrpc cid seqno PreCond PostCond) PostCond) -∗
  {{{
    PreCond args ∗
    own_rpcclient cl_ptr γrpc cid ∗
    is_RPCServer γrpc
  }}}
    RPCClient__MakeRequest #cl_ptr f (into_val.to_val args) @ k ; ⊤
  {{{ (retv:u64), RET #retv; own_rpcclient cl_ptr γrpc cid ∗ PostCond args retv }}}
  {{{ quiesceable_pre γrpc cid args PreCond PostCond }}}.
Proof using Type*.
  iIntros "#Hfspec" (Φ Φc) "!# [Hprecond [Hclerk #Hlinv]] HΦ".
  iNamed "Hclerk".

  iCache with "Hprecond HΦ".
  { (* Use PreCond to show idemp_fupd *)
    iDestruct "HΦ" as "[HΦc _]".
    iModIntro.
    iApply "HΦc".
    iModIntro.
    iIntros.
    iModIntro.
    iFrame.
    iIntros.
    iModIntro; iFrame.
  }
  wpc_rec _.
  { iFromCache. }

  iCache with "Hprecond HΦ".
  { (* Use PreCond to show idemp_fupd *)
    iDestruct "HΦ" as "[HΦc _]".
    iModIntro. iApply "HΦc".
    iModIntro. iIntros.
    iModIntro. iFrame.
    iIntros. iModIntro; iFrame.
  }
  wpc_pures.
  wpc_loadField.
  wpc_wpapply (overflow_guard_incr_spec).
  iIntros (HincrSafe).
  iNamed 1.

  wpc_pures.
  wpc_loadField.
  wpc_loadField.

  wpc_pures.
  wpc_wpapply (wp_allocStruct); first eauto.
  iIntros (req_ptr) "Hreq".
  iNamed 1.
  iDestruct (struct_fields_split with "Hreq") as "(HCID&HSeq&HArgs&_)".
  iMod (readonly_alloc_1 with "HCID") as "#HCID".
  iMod (readonly_alloc_1 with "HSeq") as "#HSeq".
  iMod (readonly_alloc_1 with "HArgs") as "#HArgs".

  wpc_pures.
  wpc_loadField.
  wpc_pures.
  wpc_storeField.
  wpc_pures.
  wpc_wpapply wp_ref_to; first eauto.
  iIntros (errb_ptr) "Herrb_ptr".
  iNamed 1.

  wpc_pures.
  wpc_wpapply (wp_allocStruct); first eauto.
  iIntros (reply_ptr) "Hreply".
  iNamed 1.
  wpc_pures.
  iDestruct (fmcounter_map_get_lb with "Hcrpc") as "#Hcseqno_lb". (* Need this to apply quiesce_idemp_1 *)

  iMod (make_request {| Req_Args:=args; Req_CID:=cid; Req_Seq:=cseqno|} (quiesce_fupd γrpc cid cseqno PreCond PostCond) PostCond with "[Hlinv] [Hcrpc] [Hprecond]") as "[Hcseq_own HallocPost]"; eauto.
  (* { admit. (* TODO: add assumption *) } *)
  { simpl. word. }
  { iIntros "??". iFrame. by iModIntro. }
  iDestruct "HallocPost" as (γP) "[#Hreqinv_init HγP]".
  (* Prepare the loop invariant *)
  iAssert (∃ (err:bool), errb_ptr ↦[boolT] #err)%I with "[Herrb_ptr]" as "Herrb_ptr".
  { iExists _. done. }
  iAssert (∃ reply', own_reply reply_ptr reply')%I with "[Hreply]" as "Hreply".
  { iDestruct (struct_fields_split with "Hreply") as "(?& ? & _)".
    iExists {| Rep_Ret:=_; Rep_Stale:=false |}. iFrame. }

  wpc_bind (For _ _ _). iApply (wpc_forBreak_cond' with "[-]").
  { by iNamedAccu. }
  {
    iNamed 1.
    iDestruct "HΦ" as "[HΦc _]".
    iModIntro.
    iApply "HΦc".
    simpl.
    iDestruct (quiesce_request with "Hlinv Hreqinv_init HγP") as "Hquiesce_req".
    iDestruct (quiesce_idemp_1 with "[] Hquiesce_req") as "HH".
    { simpl. iFrame "#". }
    iFrame.
  }
  {
    iIntros "!# __CTX"; iNamed "__CTX".

    iCache with "HγP HΦ".
    {
      iDestruct "HΦ" as "[HΦc _]".
      iModIntro. iApply "HΦc".
      iDestruct (quiesce_request with "Hlinv Hreqinv_init HγP") as "Hq".
      iDestruct (quiesce_idemp_1 with "[] Hq") as "Hq".
      { simpl. iFrame "#". }
      iFrame.
    }

    iDestruct "Hreply" as (reply') "Hreply".
    wpc_pures.
    wpc_bind (RemoteProcedureCall _ _ _). wpc_frame.
    wp_apply (RemoteProcedureCall_spec with "[] [Hreply]").
    { iSpecialize ("Hfspec" $! cseqno). iFrame "Hfspec". }
    {
      iSplit; last first.
      { unfold read_request.
        instantiate (2:={|Req_CID:=_; Req_Seq := _; Req_Args := _ |}).
        iFrame "#".
        iFrame "Hreply".
        simpl. iPureIntro. lia.
      }
      iFrame "Hreqinv_init".
    }
    iIntros (v) "Hrpc_post". iNamed 1.
    iDestruct "Herrb_ptr" as (err') "Herrb_ptr".

    iDestruct "Hrpc_post" as (reply) "[Hreply [#Hre | [#Hre HCallPost]]]".
    {
      iDestruct "Hre" as %->.

      wpc_bind (store_ty _ _).
      wpc_frame.
      wp_store.
      iNamed 1.
      wpc_pures.
      wpc_bind (load_ty _ _).
      wpc_frame.
      wp_load.
      iNamed 1.
      wpc_pures.
      iLeft.
      iFrame.
      iSplitL ""; first done.
      iSplitL "Herrb_ptr"; eauto.
    }

    iDestruct "Hre" as %->.

    wpc_bind (store_ty _ _).
    wpc_frame.
    wp_store.
    iNamed 1.

    wpc_pures.

    wpc_bind (load_ty _ _).
    wpc_frame.
    wp_load.
    iNamed 1.

    iApply wpc_fupd.
    wpc_pures.
    iRight.
    iSplitL ""; first by iModIntro.

    iDestruct "HCallPost" as "[ [_ Hbad] | #Hrcptstoro]"; simpl.
    {
      iDestruct (client_stale_seqno with "Hbad Hcseq_own") as %bad. exfalso.
      simpl in bad. replace (int.nat (word.add cseqno 1))%nat with (int.nat cseqno + 1)%nat in bad by word.
      lia.
    }

    iModIntro.
    iSplit; last first.
    {
      iLeft in "HΦ". iModIntro.
      iApply "HΦ".
      iDestruct (quiesce_request with "Hlinv Hreqinv_init HγP") as "Hq".
      iDestruct (quiesce_idemp_1 with "[] Hq") as "Hq".
      { simpl. iFrame "#". }
      iFrame.
    }

    wpc_pures.
    iNamed "Hreply".
    replace (RPCReply.S) with (lockservice_nocrash.RPCReply.S) by done.
    replace (lockservice_nocrash.RPCReply.S) with (RPCReply.S) by done.

    iApply wpc_fupd.
    wpc_frame.
    wp_loadField.
    iNamed 1.

    iMod (get_request_post with "Hreqinv_init Hrcptstoro HγP") as "HP"; first done.
    simpl.
    assert (Timeless (PostCond args reply.(Rep_Ret))) by admit. (* Timeless post *)
    iMod "HP".
    iModIntro.
    iRight in "HΦ".
    iApply "HΦ".
    iFrame.
    iExists _; iFrame.
    iPureIntro.
    word.
Admitted.
End rpc_proof.

Section kv_proof.
Context `{!heapG Σ}.
Context `{!kvserviceG Σ}.
Variable γ:kvservice_names.

Global Instance quiesceable_pre_disc cid key old_v : (Discretizable
       (quiesceable_pre γ.(ks_rpcGN) cid (key, (U64 0, ())) (Get_Pre γ old_v) (Get_Post γ old_v))).
Proof.
  rewrite /Discretizable.
  by rewrite -own_discrete_idemp.
Defined.

Global Instance quiesceable_put_disc cid args : (Discretizable
       (quiesceable_pre γ.(ks_rpcGN) cid args (Put_Pre γ) (Put_Post γ))).
Proof.
  rewrite /Discretizable.
  by rewrite -own_discrete_idemp.
Defined.

Definition own_kvclerk γ ck_ptr srv cid : iProp Σ :=
  ∃ (cl_ptr:loc),
   "Hcl_ptr" ∷ ck_ptr ↦[KVClerk.S :: "client"] #cl_ptr ∗
   "Hprimary" ∷ ck_ptr ↦[KVClerk.S :: "primary"] #srv ∗
   "Hcl" ∷ own_rpcclient cl_ptr γ.(ks_rpcGN) cid.

Lemma wpc_KVClerk__Get k E (kck srv:loc) (cid key old_v:u64) :
  is_kvserver γ srv -∗
  {{{
       own_kvclerk γ kck srv cid ∗
       quiesceable_pre γ.(ks_rpcGN) cid (key, (U64 0, ())) (Get_Pre γ old_v) (Get_Post γ old_v)
  }}}
    KVClerk__Get #kck #key @ k; E
  {{{
      RET #old_v;
      own_kvclerk γ kck srv cid ∗
      (key [[γ.(ks_kvMapGN)]]↦ old_v )
  }}}
  {{{
       quiesceable_pre γ.(ks_rpcGN) cid (key, (U64 0, ())) (Get_Pre γ old_v) (Get_Post γ old_v)
  }}}
.
Proof.
  iIntros "His_kv !#" (Φ Φc) "Hpre HΦ".
  iDestruct "Hpre" as "(Hclerk & Hq)".
  iCache with "Hq HΦ".
  {
    iDestruct "HΦ" as "[HΦc _]".
    Opaque quiesceable_pre.
    iModIntro.
    iApply "HΦc".
    done.
  }
  wpc_call.
  { done. }
  iCache with "Hq HΦ".
  {
    iDestruct "HΦ" as "[HΦc _]".
    Opaque quiesceable_pre.
    iModIntro.
    iApply "HΦc".
    done.
  }
  wpc_pures.
  iNamed "Hclerk".
  wpc_loadField.
  (* Need is_rpcHandler for KVServer__Get with quiesce_fupd pre *)
Admitted.

Lemma wpc_KVClerk__Put k E (kck srv:loc) (cid key value:u64) :
  is_kvserver γ srv -∗
  {{{
       own_kvclerk γ kck srv cid ∗
       quiesceable_pre γ.(ks_rpcGN) cid (key, (value, ())) (Put_Pre γ) (Put_Post γ)
  }}}
    KVClerk__Put #kck #key #value @ k; E
  {{{
      RET #();
      own_kvclerk γ kck srv cid ∗
      ((key [[γ.(ks_kvMapGN)]]↦ value ) ∧ quiesceable_pre γ.(ks_rpcGN) cid (key, (value, ())) (Put_Pre γ) (Put_Post γ))
  }}}
  {{{
       quiesceable_pre γ.(ks_rpcGN) cid (key, (value, ())) (Put_Pre γ) (Put_Post γ)
  }}}.
Admitted.

End kv_proof.

Section incr_proof.

(* Proof for increment backed by kv service
   requires taking
 *)

Context `{!heapG Σ}.
Context `{!filesysG Σ}.

Variable γback:kvservice_names.

Context `{!kvserviceG Σ}.

Record incrservice_names := IncrServiceGN {
  incr_rpcGN : rpc_names;
  (* fmcounter_map of key -> counter value *)
  incr_mapGN : gname;
}.

Variable γ:incrservice_names.
Variable old_v:u64.
Variable incr_cid:u64.
(* This is constant for a particular IncrServer *)

Record IncrServerC := mkIncrServserC
{
  incr_seq: u64 ;
  incr_kvserver: loc ; (* This would be an IP address or some such *)
}.

Implicit Types server : IncrServerC.

Definition IncrServer_core_own_vol (srv:loc) server : iProp Σ :=
  ∃ (kck:loc),
  "Hkvserver" ∷ srv ↦[IncrServer.S :: "kvserver"] #(server.(incr_kvserver)) ∗
  "Hkck" ∷ srv ↦[IncrServer.S :: "kck"] #kck ∗
  "#His_kvserver" ∷ is_kvserver γback server.(incr_kvserver) ∗
  "Hkck_own" ∷ own_kvclerk γback kck server.(incr_kvserver) incr_cid
  (* This is using the non-crash-safe version of kvserver in kv_proof.v *)
  .

Definition IncrServer_core_own_ghost server : iProp Σ :=
  "#His_kvserver" ∷ is_kvserver γback server.(incr_kvserver) ∗
  "Hrpcclient_own" ∷ RPCClient_own γback.(ks_rpcGN) (incr_cid) server.(incr_seq)
  (* This is using the non-crash-safe version of kvserver in kv_proof.v *)
.

Definition IncrCrashInvariant (sseq:u64) (args:RPCValC) : iProp Σ :=
  (* Case 1: Before crash barrier *)
  ("Hfown_oldv" ∷ (("incr_request_" +:+ u64_to_string sseq) +:+ "_oldv") f↦ [] ∗
   "Hq" ∷ quiesceable_pre γback.(ks_rpcGN) incr_cid args (Get_Pre γback old_v) (Get_Post γback old_v)
   ) ∨

  (* Case 2: After crash barrier *)
  ( ∃ data,
  "Hfown_oldv" ∷ (("incr_request_" +:+ u64_to_string sseq) +:+ "_oldv") f↦ data ∗
  "%Hencoding" ∷ ⌜has_encoding data [EncUInt64 old_v]⌝ ∗
   "Hq" ∷ quiesceable_pre γback.(ks_rpcGN) incr_cid (args.1, (word.add old_v 1, ())) (Put_Pre γback) (Put_Post γback)
  )
.

Instance CrashInv_disc sseq args : (Discretizable (IncrCrashInvariant sseq args)).
Proof.
Admitted.

Lemma increment_core_idempotent (isrv:loc) server (seq:u64) (args:RPCValC) :
  {{{
       IncrCrashInvariant seq args ∗
       IncrServer_core_own_vol isrv server ∗
       IncrServer_core_own_ghost server
  }}}
    IncrServer__increment_core #isrv #seq (into_val.to_val args) @ 37 ; ⊤
  {{{
      RET #0; True
  }}}
  {{{
       IncrCrashInvariant seq args ∗
       IncrServer_core_own_ghost server
  }}}.
Proof.
  iIntros (Φ Φc) "(HincrCrashInv & Hvol & Hghost) HΦ".
  wpc_call.
  { iFrame. }
  { iFrame. }
  unfold IncrCrashInvariant.
  iCache with "HincrCrashInv Hghost HΦ".
  {
    iDestruct "HΦ" as "[HΦc _]". iModIntro. iApply "HΦc".
    iFrame.
  }
  wpc_pures.

  wpc_bind (ref #0)%E.
  wpc_frame.
  wp_apply (typed_mem.wp_AllocAt).
  {
    instantiate (1:=uint64T).
    eauto.
  }
  iIntros (l) "Hl". iNamed 1.
  wpc_pures.

  wpc_bind (grove_ffi.U64ToString _).
  wpc_frame.
  wp_apply wp_U64ToString.
  iNamed 1.
  wpc_pures.

  iDestruct "HincrCrashInv" as "[Hcase|Hcase]"; iNamed "Hcase".
  { (* Case Get not done *)
    iCache with "Hfown_oldv Hq HΦ Hghost".
    {
      iDestruct "HΦ" as "[HΦc _]".
      iDestruct (own_discrete_idemp with "Hq") as "Hq".
      iModIntro. iApply "HΦc".
      iFrame. iLeft. iFrame.
    }
    (* How to get rid of bdisc: iDestruct (own_discrete_elim with "Hq") as "Hq". *)
    wpc_apply (wpc_Read with "Hfown_oldv").
    iSplit.
    { (* Show that the crash obligation of the function we're calling implies our crash obligation *)
      iDestruct "HΦ" as "[HΦc _]".
      iDestruct (own_discrete_idemp with "Hq") as "Hq".
      iModIntro. iIntros.
      iApply "HΦc".
      iFrame. iLeft. iFrame.
    }
    iNext.
    iIntros (content) "[Hcontent_slice Hfown_oldv]".
    wpc_pures.

    wpc_bind (slice.len _).
    wpc_frame.
    wp_apply wp_slice_len.
    iNamed 1.

    wpc_pures.
    iDestruct (slice.is_slice_sz with "Hcontent_slice") as "%Hslice_len".
    simpl in Hslice_len.
    assert (int.Z content.(Slice.sz) = 0) as -> by word.
    destruct bool_decide eqn:Hs.
    {
      apply bool_decide_eq_true in Hs.
      iExFalso; iPureIntro.
      done.
    }

    (* case that no durable oldv chosen *)
    wpc_pures.
    iNamed "Hvol".

    wpc_bind (struct.loadF _ _ _).
    wpc_frame.
    wp_loadField.
    iNamed 1.


    wpc_apply (wpc_KVClerk__Get with "His_kvserver [$Hkck_own $Hq]").
    iSplit.
    {
      iLeft in "HΦ".
      iModIntro. iIntros.
      iApply "HΦ".
      iFrame.
      iLeft.
      iFrame.
    }
    iNext.
    iIntros "[Hkck_own Hkvptsto]".

    iCache with "Hkvptsto HΦ Hghost Hfown_oldv".
    {
      iLeft in "HΦ".
      iModIntro.
      iApply "HΦ".
      iFrame "Hghost".
      iLeft.
      iFrame.
      (* TODO: Make a lemma that PreCond -∗ quiesceable_pre ... (PreCond) ...*)
      admit.
    }
    wpc_bind (store_ty _ _).
    wpc_frame.
    wp_store.
    iNamed 1.

    wpc_pures.
    wpc_bind (marshal.NewEnc _).
    wpc_frame.
    wp_apply (wp_new_enc).
    iIntros (enc_v) "Henc".
    iNamed 1.

    wpc_pures.
    wpc_bind (load_ty _ _).
    wpc_frame.
    wp_load.
    iNamed 1.

    wpc_bind (marshal.Enc__PutInt _ _).
    wpc_frame.
    wp_apply (wp_Enc__PutInt with "Henc"); first word.
    iIntros "Henc". iNamed 1.

    wpc_pures.
    wpc_bind (marshal.Enc__Finish _).
    wpc_frame.
    wp_apply (wp_Enc__Finish with "Henc").
    iIntros (content_slice data) "(%Hencoding & %Hlength & Hslice)".
    iNamed 1.

    wpc_apply (wpc_Write with "[$Hfown_oldv $Hslice]").
    iSplit.
    { (* Prove that if Write crashes, our crash condition is still met *)
      iLeft in "HΦ".
      iModIntro.
      iIntros "[Hfown|Hfown]".
      { (* write didn't go through *)
        iApply "HΦ".
        iFrame.
        iLeft; iFrame.
        admit. (* TODO: MakeRequest should return `PostCond ∧ quiesceable_pre`! *)
      }
      { (* Wrote oldv *)
        iApply "HΦ".
        iFrame.
        iRight.
        iExists _; iFrame.
        simpl in Hencoding.
        iSplitL ""; first done.
        (* TODO: Put_Pre -> quiesceable_pre (Put_Pre) *)
        admit.
      }
    }
    iNext.
    iIntros "[Hfown Hslice]".

    iCache with "Hfown HΦ Hghost Hkvptsto".
    {
      (* Repeat above *)
      admit.
    }

    wpc_pures.
    wpc_bind (load_ty _ _).
    wpc_frame.
    wp_load.
    iNamed 1.
    wpc_pures.

    wpc_loadField.

    wpc_apply (wpc_KVClerk__Put with "His_kvserver [$Hkck_own Hkvptsto]").
    { admit. (* TODO: quiesceable_intro *) }
    iSplit.
    {
      iLeft in "HΦ".
      iModIntro.
      iIntros.
      iApply "HΦ".
      iFrame.
      iRight.
      iExists _; iFrame.
      done.
    }
    iNext.

    iIntros "[Hkck_own HputPost]".

    wpc_pures.
    {
      iRight in "HputPost".
      iLeft in "HΦ".
      Opaque quiesceable_pre.
      iModIntro.
      iApply "HΦ".
      iFrame "Hghost".
      iRight.
      iExists _; iFrame.
      done.
    }

    iRight in "HΦ".
    iApply "HΦ".
    done.
  }
  { (* Case get already done *)
    (* TODO: Merge if/then/rest from above *)
    admit.
  }
Admitted.

End incr_proof.
